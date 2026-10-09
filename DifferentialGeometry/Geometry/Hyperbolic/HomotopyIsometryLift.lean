import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.CoveringIsometry
import DifferentialGeometry.Topology.Covering.UniversalHomotopy

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
  [LocallyPathConnectedSpace Y] [SemilocallySimplyConnectedSpace Y]

theorem exists_isometryEquiv_mapHomotopyEndpoint
    (u : C(X, Y)) (a : X ≃ᵢ Y) (H : u.Homotopy (a : C(X, Y))) (x₀ : X)
    (eX : Hyperboloid E ≃ₜ @UniversalCover X _ ⟨x₀⟩)
    (eY : Hyperboloid F ≃ₜ @UniversalCover Y _ ⟨u x₀⟩)
    (hXball : ∀ x r, 0 < r →
      (fun z => @proj X _ ⟨x₀⟩ (eX z)) '' Metric.ball x r =
        Metric.eball (@proj X _ ⟨x₀⟩ (eX x)) (ENNReal.ofReal r))
    (hYball : ∀ y r, 0 < r →
      (fun z => @proj Y _ ⟨u x₀⟩ (eY z)) '' Metric.ball y r =
        Metric.eball (@proj Y _ ⟨u x₀⟩ (eY y)) (ENNReal.ofReal r)) :
    ∃ e : Hyperboloid E ≃ᵢ Hyperboloid F,
      (∀ z, eY (e z) = mapHomotopyEndpoint H x₀ (eX z)) ∧
      (∀ z, @proj Y _ ⟨u x₀⟩ (eY (e z)) = a (@proj X _ ⟨x₀⟩ (eX z))) ∧
      (∀ (γ : FundamentalGroup X x₀) (z : Hyperboloid E),
        e (eX.symm (@deckAct X _ ⟨x₀⟩ γ (eX z))) =
          eY.symm (@deckAct Y _ ⟨u x₀⟩ (FundamentalGroup.map u x₀ γ) (eY (e z)))) := by
  let q : Hyperboloid E → X := fun z => @proj X _ ⟨x₀⟩ (eX z)
  let p : Hyperboloid F → Y := fun z => @proj Y _ ⟨u x₀⟩ (eY z)
  let f : C(Hyperboloid E, Hyperboloid F) :=
    (eY.symm : C(@UniversalCover Y _ ⟨u x₀⟩, Hyperboloid F)).comp
      ((mapHomotopyEndpoint H x₀).comp (eX : C(Hyperboloid E, @UniversalCover X _ ⟨x₀⟩)))
  have hq : IsCoveringMap q :=
    (@proj_isCoveringMap X _ ⟨x₀⟩ _ _).comp_homeomorph eX
  have hp : IsCoveringMap p :=
    (@proj_isCoveringMap Y _ ⟨u x₀⟩ _ _).comp_homeomorph eY
  have hcomm (z : Hyperboloid E) : p (f z) = a (q z) := by
    change @proj Y _ ⟨u x₀⟩ (eY (eY.symm (mapHomotopyEndpoint H x₀ (eX z)))) = _
    rw [eY.apply_symm_apply]
    exact proj_mapHomotopyEndpoint H x₀ (eX z)
  obtain ⟨e, he⟩ := Hyperboloid.exists_isometryEquiv_eq_lift q p hq hp hXball hYball a f hcomm
  have heY (z : Hyperboloid E) : eY (e z) = mapHomotopyEndpoint H x₀ (eX z) := by
    rw [he]
    exact eY.apply_symm_apply _
  refine ⟨e, heY, ?_, ?_⟩
  · intro z
    rw [heY]
    exact proj_mapHomotopyEndpoint H x₀ (eX z)
  · intro γ z
    apply eY.injective
    rw [heY, eX.apply_symm_apply, eY.apply_symm_apply, heY]
    exact mapHomotopyEndpoint_smul H x₀ γ (eX z)

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
