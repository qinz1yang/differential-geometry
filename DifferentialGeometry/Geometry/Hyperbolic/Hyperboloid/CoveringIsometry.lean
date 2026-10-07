import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Lipschitz
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.Lifting

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem lipschitzWith_one_of_image_ball
    {X B : Type*} [PseudoMetricSpace X] [PseudoEMetricSpace B] (p : X → B)
    (hball : ∀ x r, 0 < r → p '' Metric.ball x r = Metric.eball (p x) (ENNReal.ofReal r)) :
    LipschitzWith 1 p := by
  intro x y
  simp only [ENNReal.coe_one, one_mul]
  by_contra h
  obtain ⟨r, _, hxy, hrp⟩ := ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge h)
  have hr : 0 < r := ENNReal.ofReal_pos.mp (zero_le.trans_lt hxy)
  have hym : y ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_comm]
    exact edist_lt_ofReal.mp hxy
  have hpym : p y ∈ Metric.eball (p x) (ENNReal.ofReal r) := by
    rw [← hball x r hr]
    exact ⟨y, hym, rfl⟩
  have hlt : edist (p x) (p y) < ENNReal.ofReal r := by
    simpa only [Metric.mem_eball, edist_comm] using hpym
  exact (lt_irrefl _) (hlt.trans hrp)

theorem exists_isometryEquiv_eq_lift
    {A B : Type*} [PseudoEMetricSpace A] [PseudoEMetricSpace B]
    (q : Hyperboloid E → A) (p : Hyperboloid F → B)
    (hq : IsCoveringMap q) (hp : IsCoveringMap p)
    (hqball : ∀ x r, 0 < r → q '' Metric.ball x r = Metric.eball (q x) (ENNReal.ofReal r))
    (hpball : ∀ y r, 0 < r → p '' Metric.ball y r = Metric.eball (p y) (ENNReal.ofReal r))
    (a : A ≃ᵢ B) (f : C(Hyperboloid E, Hyperboloid F))
    (hcomm : ∀ x, p (f x) = a (q x)) :
    ∃ e : Hyperboloid E ≃ᵢ Hyperboloid F, ∀ x, e x = f x := by
  let _ : ContractibleSpace (Hyperboloid E) := spaceHomeomorph.contractibleSpace
  let _ : ContractibleSpace (Hyperboloid F) := spaceHomeomorph.contractibleSpace
  let _ : LocallyPathConnectedSpace (Hyperboloid F) :=
    (spaceHomeomorph (E := F)).symm.locallyPathConnectedSpace
  let b : C(Hyperboloid F, A) :=
    (a.symm : C(B, A)).comp ⟨p, hp.continuous⟩
  have hb : q origin = b (f origin) := by
    change q origin = a.symm (p (f origin))
    rw [hcomm, a.symm_apply_apply]
  obtain ⟨g, ⟨hg0, hgproj⟩, _⟩ := hq.existsUnique_continuousMap_lifts b (f origin) origin hb
  have hgpoint (y : Hyperboloid F) : q (g y) = a.symm (p y) := congrFun hgproj y
  have hleft : Function.LeftInverse g f := by
    have hgf : (g : Hyperboloid F → Hyperboloid E) ∘ f = id := hq.eq_of_comp_eq
      (g.continuous.comp f.continuous) continuous_id
      (by
        funext x
        change q (g (f x)) = q x
        rw [hgpoint, hcomm, a.symm_apply_apply]) origin hg0
    exact fun x => congrFun hgf x
  have hright : Function.RightInverse g f := by
    have hfg : (f : Hyperboloid E → Hyperboloid F) ∘ g = id := hp.eq_of_comp_eq
      (f.continuous.comp g.continuous) continuous_id
      (by
        funext y
        change p (f (g y)) = p y
        rw [hcomm, hgpoint, a.apply_symm_apply]) (f origin)
      (by change f (g (f origin)) = f origin; rw [hg0])
    exact fun y => congrFun hfg y
  have hqLip := lipschitzWith_one_of_image_ball q hqball
  have hpLip := lipschitzWith_one_of_image_ball p hpball
  have hfLip : LipschitzWith 1 f := lipschitzWith_lift_of_image_ball
    f.continuous hp.isLocalHomeomorph.isLocallyInjective hpball hcomm hqLip a.isometry.lipschitzWith
  have hgLip : LipschitzWith 1 g := lipschitzWith_lift_of_image_ball
    g.continuous hq.isLocalHomeomorph.isLocallyInjective hqball hgpoint hpLip a.symm.isometry.lipschitzWith
  have hiso : Isometry f := by
    intro x y
    apply le_antisymm
    · simpa only [ENNReal.coe_one, one_mul] using hfLip x y
    · simpa only [hleft x, hleft y, ENNReal.coe_one, one_mul] using hgLip (f x) (f y)
  let e : Hyperboloid E ≃ᵢ Hyperboloid F :=
    { toEquiv := Equiv.ofBijective f ⟨hleft.injective, hright.surjective⟩
      isometry_toFun := hiso }
  exact ⟨e, fun _ => rfl⟩

end DifferentialGeometry.Hyperboloid
