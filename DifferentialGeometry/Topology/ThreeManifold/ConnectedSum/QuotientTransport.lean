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

universe u

def puncturedHomeomorphOfImage {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c c' : BallChart n (𝓡 n) M) (Φ : M ≃ₜ M)
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
  have hmem' : ∀ y : c'.Punctured, Φ.symm (y : M) ∉
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

universe u v

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]

def homeomorphOfPuncturedHomeomorph
    (c c' : BallChart 3 (𝓡 3) M) (d d' : BallChart 3 (𝓡 3) N)
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
    (c c' : BallChart 3 (𝓡 3) M) (d d' : BallChart 3 (𝓡 3) N)
    (a a' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (Φ : M ≃ₜ M) (Ψ : N ≃ₜ N)
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
