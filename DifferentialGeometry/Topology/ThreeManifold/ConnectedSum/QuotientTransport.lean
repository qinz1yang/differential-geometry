import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u v w u' v' w'

def adjunctionSpaceHomeomorphOfHomeomorph
    {A : Type u} {B : Type v} {X : Type w}
    {A' : Type u'} {B' : Type v'} {X' : Type w'}
    [TopologicalSpace A] [TopologicalSpace A']
    [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace B'] [TopologicalSpace X']
    (i : A → B) (φ : A → X) (i' : A' → B') (φ' : A' → X')
    (eA : A ≃ₜ A') (eB : B ≃ₜ B') (eX : X ≃ₜ X')
    (hi : ∀ a, eB (i a) = i' (eA a)) (hφ : ∀ a, eX (φ a) = φ' (eA a)) :
    AdjunctionSpace i φ ≃ₜ AdjunctionSpace i' φ' := by
  classical
  have hcoh : ∀ a, adjunctionCell i' φ' (eB (i a)) = adjunctionLower φ' (eX (φ a)) :=
    fun a => (congrArg (adjunctionCell i' φ') (hi a)).trans
      ((adjunction_coherence i' φ' (eA a)).trans
        (congrArg (adjunctionLower φ') (hφ a)).symm)
  let Ffun : B ⊕ X → AdjunctionSpace i' φ' :=
    Sum.elim (fun b => adjunctionCell i' φ' (eB b)) (fun x => adjunctionLower φ' (eX x))
  have hFrel : ∀ a b, adjunctionRel i φ a b → Ffun a = Ffun b := by
    rintro a b ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hcoh z
    · exact (hcoh z).symm
  let F : AdjunctionSpace i φ → AdjunctionSpace i' φ' := Quot.lift Ffun hFrel
  have hFcont : Continuous F :=
    continuous_adjunction_lift i φ hFrel
      (Continuous.sumElim ((continuous_adjunctionCell i' φ').comp eB.continuous)
        ((continuous_adjunctionLower i' φ').comp eX.continuous))
  have hisymm : ∀ a', eB.symm (i' a') = i (eA.symm a') := by
    intro a'
    refine eB.symm_apply_eq.mpr ?_
    rw [hi (eA.symm a'), eA.apply_symm_apply]
  have hφsymm : ∀ a', eX.symm (φ' a') = φ (eA.symm a') := by
    intro a'
    refine eX.symm_apply_eq.mpr ?_
    rw [hφ (eA.symm a'), eA.apply_symm_apply]
  have hcoh' : ∀ a', adjunctionCell i φ (eB.symm (i' a')) =
      adjunctionLower φ (eX.symm (φ' a')) :=
    fun a' => (congrArg (adjunctionCell i φ) (hisymm a')).trans
      ((adjunction_coherence i φ (eA.symm a')).trans
        (congrArg (adjunctionLower φ) (hφsymm a')).symm)
  let Gfun : B' ⊕ X' → AdjunctionSpace i φ :=
    Sum.elim (fun b => adjunctionCell i φ (eB.symm b)) (fun x => adjunctionLower φ (eX.symm x))
  have hGrel : ∀ a b, adjunctionRel i' φ' a b → Gfun a = Gfun b := by
    rintro a b ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hcoh' z
    · exact (hcoh' z).symm
  let G : AdjunctionSpace i' φ' → AdjunctionSpace i φ := Quot.lift Gfun hGrel
  have hGcont : Continuous G :=
    continuous_adjunction_lift i' φ' hGrel
      (Continuous.sumElim ((continuous_adjunctionCell i φ).comp eB.symm.continuous)
        ((continuous_adjunctionLower i φ).comp eX.symm.continuous))
  have hFcell : ∀ b, F (adjunctionCell i φ b) = adjunctionCell i' φ' (eB b) := fun b => rfl
  have hFlower : ∀ x, F (adjunctionLower φ x) = adjunctionLower φ' (eX x) := fun x => rfl
  have hGcell : ∀ b', G (adjunctionCell i' φ' b') = adjunctionCell i φ (eB.symm b') := fun b' => rfl
  have hGlower : ∀ x', G (adjunctionLower φ' x') = adjunctionLower φ (eX.symm x') := fun x' => rfl
  have hleft : Function.LeftInverse G F := by
    intro z
    induction z using Quot.induction_on with
    | _ s =>
      cases s with
      | inl b =>
        change G (F (adjunctionCell i φ b)) = adjunctionCell i φ b
        rw [hFcell, hGcell, eB.symm_apply_apply]
      | inr x =>
        change G (F (adjunctionLower φ x)) = adjunctionLower φ x
        rw [hFlower, hGlower, eX.symm_apply_apply]
  have hright : Function.RightInverse G F := by
    intro z
    induction z using Quot.induction_on with
    | _ s =>
      cases s with
      | inl b =>
        change F (G (adjunctionCell i' φ' b)) = adjunctionCell i' φ' b
        rw [hGcell, hFcell, eB.apply_symm_apply]
      | inr x =>
        change F (G (adjunctionLower φ' x)) = adjunctionLower φ' x
        rw [hGlower, hFlower, eX.apply_symm_apply]
  exact Homeomorph.mk
    { toFun := F, invFun := G, left_inv := hleft, right_inv := hright } hFcont hGcont

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u v w u' v' w'

def adjunctionSpaceHomeomorphOfRelHomeomorph
    {A : Type u} {B : Type v} {X : Type w}
    {A' : Type u'} {B' : Type v'} {X' : Type w'}
    [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace B'] [TopologicalSpace X']
    (i : A → B) (φ : A → X) (i' : A' → B') (φ' : A' → X')
    (e : B ⊕ X ≃ₜ B' ⊕ X')
    (h : ∀ u v, adjunctionRel i φ u v → adjunctionRel i' φ' (e u) (e v))
    (h' : ∀ u v, adjunctionRel i' φ' u v → adjunctionRel i φ (e.symm u) (e.symm v)) :
    AdjunctionSpace i φ ≃ₜ AdjunctionSpace i' φ' := by
  classical
  have hFrel : ∀ u v, adjunctionRel i φ u v →
      adjunctionMk i' φ' (e u) = adjunctionMk i' φ' (e v) :=
    fun u v huv => Quot.sound (h u v huv)
  let F : AdjunctionSpace i φ → AdjunctionSpace i' φ' :=
    Quot.lift (fun s => adjunctionMk i' φ' (e s)) hFrel
  have hFcont : Continuous F :=
    continuous_adjunction_lift i φ hFrel ((continuous_adjunctionMk i' φ').comp e.continuous)
  have hGrel : ∀ u v, adjunctionRel i' φ' u v →
      adjunctionMk i φ (e.symm u) = adjunctionMk i φ (e.symm v) :=
    fun u v huv => Quot.sound (h' u v huv)
  let G : AdjunctionSpace i' φ' → AdjunctionSpace i φ :=
    Quot.lift (fun s => adjunctionMk i φ (e.symm s)) hGrel
  have hGcont : Continuous G :=
    continuous_adjunction_lift i' φ' hGrel ((continuous_adjunctionMk i φ).comp e.symm.continuous)
  have hleft : Function.LeftInverse G F := by
    intro z
    induction z using Quot.induction_on with
    | _ s =>
      change Quot.mk (adjunctionRel i φ) (e.symm (e s)) = Quot.mk (adjunctionRel i φ) s
      rw [e.symm_apply_apply]
  have hright : Function.RightInverse G F := by
    intro z
    induction z using Quot.induction_on with
    | _ s =>
      change Quot.mk (adjunctionRel i' φ') (e (e.symm s)) = Quot.mk (adjunctionRel i' φ') s
      rw [e.apply_symm_apply]
  exact Homeomorph.mk
    { toFun := F, invFun := G, left_inv := hleft, right_inv := hright } hFcont hGcont

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]

def commHomeomorph (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ConnectedSumQuotient c d a ≃ₜ ConnectedSumQuotient d c a.symm := by
  refine adjunctionSpaceHomeomorphOfRelHomeomorph c.boundaryMap (d.boundaryMap ∘ a)
    d.boundaryMap (c.boundaryMap ∘ a.symm)
    (Homeomorph.sumComm _ _) ?_ ?_
  · rintro u v ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · refine ⟨a z, Or.inr ⟨?_, ?_⟩⟩
      · simp only [Function.comp_apply, Homeomorph.coe_sumComm, Sum.swap_inr]
      · simp only [Function.comp_apply, Homeomorph.coe_sumComm, Sum.swap_inl]
        rw [a.symm_apply_apply]
    · refine ⟨a z, Or.inl ⟨?_, ?_⟩⟩
      · simp only [Function.comp_apply, Homeomorph.coe_sumComm, Sum.swap_inr]
      · simp only [Function.comp_apply, Homeomorph.coe_sumComm, Sum.swap_inl]
        rw [a.symm_apply_apply]
  · rintro u v ⟨z, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · refine ⟨a.symm z, Or.inr ⟨?_, ?_⟩⟩
      · simp only [Function.comp_apply, Homeomorph.sumComm_symm, Homeomorph.coe_sumComm,
          Sum.swap_inr]
      · simp only [Function.comp_apply, Homeomorph.sumComm_symm, Homeomorph.coe_sumComm,
          Sum.swap_inl]
        rw [a.apply_symm_apply]
    · refine ⟨a.symm z, Or.inl ⟨?_, ?_⟩⟩
      · simp only [Function.comp_apply, Homeomorph.sumComm_symm, Homeomorph.coe_sumComm,
          Sum.swap_inr]
      · simp only [Function.comp_apply, Homeomorph.sumComm_symm, Homeomorph.coe_sumComm,
          Sum.swap_inl]
        rw [a.apply_symm_apply]

end DifferentialGeometry.Topology.ConnectedSumQuotient

namespace DifferentialGeometry.Topology.BallChart

universe u u'

def puncturedHomeomorphOfImage {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {M' : Type u'} [TopologicalSpace M'] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M']
    (c : BallChart n (𝓡 n) M) (c' : BallChart n (𝓡 n) M') (Φ : M ≃ₜ M')
    (hΦ : Φ '' (c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) =
      c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    c.Punctured ≃ₜ c'.Punctured := by
  have key : ∀ x : M, Φ x ∈ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ↔
      x ∈ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro x
    rw [← hΦ]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [Φ.injective hyx] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hmem : ∀ x : c.Punctured, Φ (x : M) ∉
      c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    fun x h => x.2 ((key x).mp h)
  have hmem' : ∀ y : c'.Punctured, Φ.symm (y : M') ∉
      c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    fun y h => y.2 (by
      rw [← Φ.apply_symm_apply y]
      exact (key (Φ.symm y)).mpr h)
  refine Homeomorph.mk
    { toFun := fun x => ⟨Φ x, hmem x⟩
      invFun := fun y => ⟨Φ.symm y, hmem' y⟩
      left_inv := fun x => Subtype.ext (Φ.left_inv x)
      right_inv := fun y => Subtype.ext (Φ.right_inv y) }
    (Continuous.subtype_mk (Φ.continuous.comp continuous_subtype_val) hmem)
    (Continuous.subtype_mk (Φ.symm.continuous.comp continuous_subtype_val) hmem')

end DifferentialGeometry.Topology.BallChart

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v u' v'

variable {M : Type u} {N : Type v} {M' : Type u'} {N' : Type v'}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [TopologicalSpace M'] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M']
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [TopologicalSpace N'] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N']

def homeomorphOfPuncturedHomeomorph
    (c : BallChart 3 (𝓡 3) M) (c' : BallChart 3 (𝓡 3) M')
    (d : BallChart 3 (𝓡 3) N) (d' : BallChart 3 (𝓡 3) N')
    (a a' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (eB : c.Punctured ≃ₜ c'.Punctured) (eX : d.Punctured ≃ₜ d'.Punctured)
    (eS : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hB : ∀ z, eB (c.boundaryMap z) = c'.boundaryMap (eS z))
    (hX : ∀ z, eX (d.boundaryMap (a z)) = d'.boundaryMap (a' (eS z))) :
    ConnectedSumQuotient c d a ≃ₜ ConnectedSumQuotient c' d' a' :=
  adjunctionSpaceHomeomorphOfHomeomorph c.boundaryMap (d.boundaryMap ∘ a)
    c'.boundaryMap (d'.boundaryMap ∘ a') eS eB eX hB hX

def homeomorphOfBallImage
    (c : BallChart 3 (𝓡 3) M) (c' : BallChart 3 (𝓡 3) M')
    (d : BallChart 3 (𝓡 3) N) (d' : BallChart 3 (𝓡 3) N')
    (a a' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (Φ : M ≃ₜ M') (Ψ : N ≃ₜ N')
    (hΦ : Φ '' (c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hΨ : Ψ '' (d.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      d'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (eS : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hB : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Φ (c.chart z) = c'.chart (eS z))
    (hX : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Ψ (d.chart (a z)) = d'.chart (a' (eS z))) :
    ConnectedSumQuotient c d a ≃ₜ ConnectedSumQuotient c' d' a' := by
  refine homeomorphOfPuncturedHomeomorph c c' d d' a a'
    (BallChart.puncturedHomeomorphOfImage c c' Φ hΦ)
    (BallChart.puncturedHomeomorphOfImage d d' Ψ hΨ) eS ?_ ?_
  · intro z
    apply Subtype.ext
    change Φ (c.chart z) = c'.chart (eS z)
    exact hB z
  · intro z
    apply Subtype.ext
    change Ψ (d.chart (a z)) = d'.chart (a' (eS z))
    exact hX z

end DifferentialGeometry.Topology.ConnectedSumQuotient

namespace DifferentialGeometry.Topology

universe u v u' v'

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem connectedSum_homeomorph_of_ballChart_agreement
    (M : ConnectedClosedOrientedManifold.{u} 3) (M' : ConnectedClosedOrientedManifold.{u'} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) (N' : ConnectedClosedOrientedManifold.{v'} 3)
    (Φ : M.Carrier ≃ₜ M'.Carrier) (Ψ : N.Carrier ≃ₜ N'.Carrier)
    (hΦ : ∀ x ∈ Metric.closedBall (0 : E3) 1,
      Φ ((orientedBallChart M).toBallChart.chart x) =
        (orientedBallChart M').toBallChart.chart x)
    (hΨ : ∀ x ∈ Metric.closedBall (0 : E3) 1,
      Ψ ((orientedBallChart N).toBallChart.chart x) =
        (orientedBallChart N').toBallChart.chart x) :
    Nonempty ((connectedSum M N).Carrier ≃ₜ (connectedSum M' N').Carrier) := by
  let c := (orientedBallChart M).toBallChart
  let c' := (orientedBallChart M').toBallChart
  let d := (orientedBallChart N).toBallChart
  let d' := (orientedBallChart N').toBallChart
  let a := boundaryAttachment.1.toHomeomorph
  have hclosed : ∀ z : Metric.sphere (0 : E3) 1, (z : E3) ∈ Metric.closedBall (0 : E3) 1 :=
    fun z => Metric.sphere_subset_closedBall z.2
  have hballM : Φ '' (c.chart '' Metric.ball (0 : E3) 1) =
      c'.chart '' Metric.ball (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hΦ x (Metric.ball_subset_closedBall hx)).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨c.chart x, ⟨x, hx, rfl⟩, hΦ x (Metric.ball_subset_closedBall hx)⟩
  have hballN : Ψ '' (d.chart '' Metric.ball (0 : E3) 1) =
      d'.chart '' Metric.ball (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hΨ x (Metric.ball_subset_closedBall hx)).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨d.chart x, ⟨x, hx, rfl⟩, hΨ x (Metric.ball_subset_closedBall hx)⟩
  have hB : ∀ z : Metric.sphere (0 : E3) 1,
      Φ (c.chart (z : E3)) = c'.chart ((Homeomorph.refl (Metric.sphere (0 : E3) 1)) z : E3) :=
    fun z => hΦ (z : E3) (hclosed z)
  have hX : ∀ z : Metric.sphere (0 : E3) 1,
      Ψ (d.chart (a z : E3)) =
        d'.chart (a ((Homeomorph.refl (Metric.sphere (0 : E3) 1)) z) : E3) :=
    fun z => hΨ (a z : E3) (hclosed (a z))
  exact ⟨ConnectedSumQuotient.homeomorphOfBallImage c c' d d' a a Φ Ψ hballM hballN
    (Homeomorph.refl _) hB hX⟩

theorem connectedSum_homeomorph_comm (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3) :
    Nonempty ((connectedSum M N).Carrier ≃ₜ (connectedSum N M).Carrier) := by
  have hsymm : (boundaryAttachment.1.toHomeomorph).symm = boundaryAttachment.1.toHomeomorph := by
    rw [← Diffeomorph.symm_toHomeomorph, boundaryAttachment_symm]
  have h := ConnectedSumQuotient.commHomeomorph (orientedBallChart M).toBallChart
    (orientedBallChart N).toBallChart boundaryAttachment.1.toHomeomorph
  rw [hsymm] at h
  exact ⟨h⟩

end DifferentialGeometry.Topology

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

theorem chart_image_ball_of_closedBall_two
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c c' : BallChart 3 (𝓡 3) M) (Φ : M → M)
    (hΦ : ∀ x : EuclideanSpace ℝ (Fin 3), x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 →
      Φ (c.chart x) = c'.chart x) :
    Φ '' (c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (hΦ x (Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.ball_subset_closedBall hx))).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c.chart x, ⟨x, hx, rfl⟩,
      hΦ x (Metric.closedBall_subset_closedBall (by norm_num) (Metric.ball_subset_closedBall hx))⟩

theorem chart_sphere_agreement_of_closedBall_two
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c c' : BallChart 3 (𝓡 3) M) (Φ : M → M)
    (hΦ : ∀ x : EuclideanSpace ℝ (Fin 3), x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 →
      Φ (c.chart x) = c'.chart x)
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Φ (c.chart (z : EuclideanSpace ℝ (Fin 3))) = c'.chart (z : EuclideanSpace ℝ (Fin 3)) :=
  hΦ (z : EuclideanSpace ℝ (Fin 3)) (Metric.closedBall_subset_closedBall (by norm_num)
    (Metric.sphere_subset_closedBall z.2))

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u

variable {M N : Type u} [TopologicalSpace M] [ChartedSpace csModel M]
  [TopologicalSpace N] [ChartedSpace csModel N]
  (c c' : BallChart 3 (𝓡 3) M) (d d' : BallChart 3 (𝓡 3) N)
  (a : csSphere ≃ₜ csSphere)
  (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (Ψ : Diffeomorph (𝓡 3) (𝓡 3) N N ∞)
  (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 →
    Φ (c.chart x) = c'.chart x)
  (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 →
    Ψ (d.chart x) = d'.chart x)

def homeomorphOfClosedBallTwoAgreement :
    ConnectedSumQuotient c d a ≃ₜ ConnectedSumQuotient c' d' a :=
  homeomorphOfBallImage c c' d d' a a Φ.toHomeomorph Ψ.toHomeomorph
    (chart_image_ball_of_closedBall_two c c' Φ hΦ)
    (chart_image_ball_of_closedBall_two d d' Ψ hΨ)
    (Homeomorph.refl csSphere)
    (fun z => by simpa using chart_sphere_agreement_of_closedBall_two c c' Φ hΦ z)
    (fun z => by simpa using chart_sphere_agreement_of_closedBall_two d d' Ψ hΨ (a z))

theorem homeomorphOfClosedBallTwoAgreement_inl (y : c.Punctured) :
    homeomorphOfClosedBallTwoAgreement c c' d d' a Φ Ψ hΦ hΨ (inl c d a y)
      = inl c' d' a
        (BallChart.puncturedHomeomorphOfImage c c' Φ.toHomeomorph
          (chart_image_ball_of_closedBall_two c c' Φ hΦ) y) :=
  rfl

theorem homeomorphOfClosedBallTwoAgreement_inr (y : d.Punctured) :
    homeomorphOfClosedBallTwoAgreement c c' d d' a Φ Ψ hΦ hΨ (inr c d a y)
      = inr c' d' a
        (BallChart.puncturedHomeomorphOfImage d d' Ψ.toHomeomorph
          (chart_image_ball_of_closedBall_two d d' Ψ hΨ) y) :=
  rfl

theorem homeomorphOfClosedBallTwoAgreement_seamLeft (x : Seam) :
    homeomorphOfClosedBallTwoAgreement c c' d d' a Φ Ψ hΦ hΨ (seamLeft c d a x)
      = seamLeft c' d' a x := by
  have hball : (max 1 ‖(x : csModel)‖) • (seamDir x : csModel)
      ∈ Metric.closedBall (0 : csModel) 2 := by
    have hr0 : 0 ≤ max 1 ‖(x : csModel)‖ := le_trans zero_le_one (le_max_left _ _)
    have hrmax : max 1 ‖(x : csModel)‖ ≤ 3 / 2 := max_le (by norm_num) (le_of_lt x.2.2)
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr0,
      norm_coe_sphere, mul_one]
    exact le_trans hrmax (by norm_num)
  simp only [seamLeft]
  rw [homeomorphOfClosedBallTwoAgreement_inl]
  refine congrArg (inl c' d' a) ?_
  refine Subtype.ext ?_
  exact hΦ _ hball

theorem homeomorphOfClosedBallTwoAgreement_seamRight (x : Seam) :
    homeomorphOfClosedBallTwoAgreement c c' d d' a Φ Ψ hΦ hΨ (seamRight c d a x)
      = seamRight c' d' a x := by
  have hz : ‖(a (seamDir x) : csModel)‖ = 1 := norm_coe_sphere _
  have hball : (max 1 (2 - ‖(x : csModel)‖)) • (a (seamDir x) : csModel)
      ∈ Metric.closedBall (0 : csModel) 2 := by
    have hr0 : 0 ≤ max 1 (2 - ‖(x : csModel)‖) := le_trans zero_le_one (le_max_left _ _)
    have hrmax : max 1 (2 - ‖(x : csModel)‖) ≤ 3 / 2 :=
      max_le (by norm_num) (by linarith [x.2.1])
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr0, hz, mul_one]
    exact le_trans hrmax (by norm_num)
  simp only [seamRight]
  rw [homeomorphOfClosedBallTwoAgreement_inr]
  refine congrArg (inr c' d' a) ?_
  refine Subtype.ext ?_
  exact hΨ _ hball

theorem homeomorphOfClosedBallTwoAgreement_seamMap (x : Seam) :
    homeomorphOfClosedBallTwoAgreement c c' d d' a Φ Ψ hΦ hΨ (seamMap c d a x)
      = seamMap c' d' a x := by
  simp only [seamMap]
  split_ifs
  · exact homeomorphOfClosedBallTwoAgreement_seamLeft c c' d d' a Φ Ψ hΦ hΨ x
  · exact homeomorphOfClosedBallTwoAgreement_seamRight c c' d d' a Φ Ψ hΦ hΨ x

end DifferentialGeometry.Topology.ConnectedSumQuotient


namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u

variable {M N : Type u} [TopologicalSpace M] [ChartedSpace csModel M]
  [TopologicalSpace N] [ChartedSpace csModel N]
  (c c' : BallChart 3 (𝓡 3) M) (d d' : BallChart 3 (𝓡 3) N)
  (a : csSphere ≃ₜ csSphere)
  (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M ∞) (Ψ : Diffeomorph (𝓡 3) (𝓡 3) N N ∞)
  (hΦ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 →
    Φ (c.chart x) = c'.chart x)
  (hΨ : ∀ x : csModel, x ∈ Metric.closedBall (0 : csModel) 2 →
    Ψ (d.chart x) = d'.chart x)

theorem seamChartX_comp_homeomorphOfClosedBallTwoAgreement (y : ConnectedSumQuotient c d a)
    (hy : y ∈ (seamChartX c d a).source) :
    seamChartX c' d' a
        (homeomorphOfClosedBallTwoAgreement c c' d d' a Φ Ψ hΦ hΨ y)
      = seamChartX c d a y := by
  rw [seamChartX_source] at hy
  obtain ⟨x, rfl⟩ := hy
  rw [homeomorphOfClosedBallTwoAgreement_seamMap]
  rw [seamChartX_apply_seamMap, seamChartX_apply_seamMap]

end DifferentialGeometry.Topology.ConnectedSumQuotient
