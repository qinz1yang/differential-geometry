import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section

namespace Bundle.RiemannianMetric

section Pullback

variable {B C : Type*} {V : B → Type*} {W : C → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]

@[ext]
theorem ext {g h : RiemannianMetric V}
    (hinner : ∀ x v w, g.inner x v w = h.inner x v w) : g = h := by
  cases g
  cases h
  congr 1
  funext x
  ext v w
  exact hinner x v w

def pullback (g : RiemannianMetric W) (f : B → C) (e : ∀ x, V x ≃L[ℝ] W (f x)) :
    RiemannianMetric V where
  inner x := (ContinuousLinearMap.precomp ℝ (e x).toContinuousLinearMap).comp
    ((g.inner (f x)).comp (e x).toContinuousLinearMap)
  symm x v w := g.symm (f x) (e x v) (e x w)
  pos x v hv := g.pos (f x) (e x v) ((e x).map_ne_zero_iff.mpr hv)
  continuousAt x := by
    have hg : ContinuousAt (fun w => g.inner (f x) w w) (e x 0) := by
      simpa only [map_zero] using g.continuousAt (f x)
    exact hg.comp (e x).continuous.continuousAt
  isVonNBounded x := by
    have h := (g.isVonNBounded (f x)).image (e x).symm.toContinuousLinearMap
    have heq : {v : V x | g.inner (f x) (e x v) (e x v) < 1} =
        (e x).symm '' {w : W (f x) | g.inner (f x) w w < 1} := by
      ext v
      constructor
      · intro hv
        exact ⟨e x v, hv, (e x).symm_apply_apply v⟩
      · rintro ⟨w, hw, rfl⟩
        change g.inner (f x) (e x ((e x).symm w)) (e x ((e x).symm w)) < 1
        simpa only [(e x).apply_symm_apply, Set.mem_ofPred_eq] using hw
    change Bornology.IsVonNBounded ℝ {v : V x | g.inner (f x) (e x v) (e x v) < 1}
    rw [heq]
    exact h

@[simp]
theorem pullback_inner (g : RiemannianMetric W) (f : B → C)
    (e : ∀ x, V x ≃L[ℝ] W (f x)) (x : B) (v w : V x) :
    (g.pullback f e).inner x v w = g.inner (f x) (e x v) (e x w) := rfl

@[simp]
theorem pullback_id (g : RiemannianMetric V) :
    g.pullback id (fun x => ContinuousLinearEquiv.refl ℝ (V x)) = g := by
  apply ext
  intro x v w
  rfl

theorem pullback_comp {A : Type*} {U : A → Type*}
    [∀ x, AddCommGroup (U x)] [∀ x, Module ℝ (U x)] [∀ x, TopologicalSpace (U x)]
    (g : RiemannianMetric W) (f : B → C) (e : ∀ x, V x ≃L[ℝ] W (f x))
    (q : A → B) (d : ∀ x, U x ≃L[ℝ] V (q x)) :
    (g.pullback f e).pullback q d =
      g.pullback (f ∘ q) (fun x => (d x).trans (e (q x))) := by
  apply ext
  intro x v w
  rfl

end Pullback

section InnerProduct

variable {B : Type*} (V : B → Type*)
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]

def ofInnerProductSpace : RiemannianMetric V where
  inner _ := innerSL ℝ
  symm _ v w := real_inner_comm w v
  pos _ _ hv := real_inner_self_pos.mpr hv
  continuousAt _ := (continuous_id.inner continuous_id).continuousAt
  isVonNBounded x := by
    have hset : {v : V x | Inner.inner ℝ v v < 1} = Metric.ball 0 1 := by
      ext v
      simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right, real_inner_self_eq_norm_sq]
      constructor <;> intro h <;> nlinarith [norm_nonneg v]
    change Bornology.IsVonNBounded ℝ {v : V x | Inner.inner ℝ v v < 1}
    rw [hset]
    exact NormedSpace.isVonNBounded_ball ℝ (V x) 1

@[simp]
theorem ofInnerProductSpace_inner (x : B) (v w : V x) :
    (ofInnerProductSpace V).inner x v w = Inner.inner ℝ v w := rfl

end InnerProduct

end Bundle.RiemannianMetric
