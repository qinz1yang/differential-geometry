import DifferentialGeometry.Tensor.RicciIdentity.OneForm
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamily
import DifferentialGeometry.Geometry.Metric.TensorNormJointSmoothness

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

structure IsHeatOneFormOn
    [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (h : Real -> OneFormSection (I := I) (M := M))
    (nablaH : Real -> TwoTensorSection (I := I) (M := M))
    (nabla2H : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) : Prop where
  realizes :
    forall t : RealTimeInterval.FlowTime D, forall x : M,
      Nabla2OneFormRealizesAt (I := I) (G.connection (t : Real))
        (h (t : Real)) (nablaH (t : Real)) x (nabla2H (t : Real) x)
  equation :
    forall t : RealTimeInterval.RegularTime D, forall (x : M) (X : TangentSpace I x),
      HasDerivAt (fun s : Real => h s x (fun _ : Fin 1 => X))
        (roughLap0STensor (I := I) (G.metric (t : Real)) (s := 1)
          (nabla2H (t : Real) x) (fun _ : Fin 1 => X))
        (t : Real)
  jointSmooth :
    forall {Idx : Type} [Fintype Idx]
      (frame : Idx -> (x : M) -> TangentSpace I x) {u : Set M},
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u ->
      forall i : Idx,
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M => h p.1 p.2 (fun _ : Fin 1 => frame i p.2))
          (D.regular ×ˢ u)
  jointSmoothNabla :
    forall {Idx : Type} [Fintype Idx]
      (frame : Idx -> (x : M) -> TangentSpace I x) {u : Set M},
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u ->
      forall i j : Idx,
        ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
          (fun p : Real × M =>
            nablaH p.1 p.2 (vec2 (frame i p.2) (frame j p.2)))
          (D.regular ×ˢ u)


theorem heatOneForm_normSq_jointContMDiffOn
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {h : ℝ → OneFormSection (I := I) (M := M)}
    {nablaH : ℝ → TwoTensorSection (I := I) (M := M)}
    {nabla2H : ℝ → (x : M) →
      Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3 x}
    (hHeat : IsHeatOneFormOn (I := I) G h nablaH nabla2H) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S (I := I) (G.metric p.1) p.2 1 (h p.1 p.2))
      (D.regular ×ˢ (Set.univ : Set M)) := by
  refine Tensor0SBundle.normSq0S_jointContMDiffOn (fun t => G.metric t) 1 (fun t x => h t x)
    D.regular_isOpen ?_ ?_
  · exact hG.frameCompSmooth
  · intro Idx _ frame u hframe m
    refine (hHeat.jointSmooth frame hframe (m 0)).congr (fun p _ => ?_)
    change h p.1 p.2 (fun a : Fin 1 => frame (m a) p.2)
        = h p.1 p.2 (fun _ : Fin 1 => frame (m 0) p.2)
    congr 1
    funext a
    rw [Subsingleton.elim a 0]

theorem heatOneForm_nablaNormSq_jointContMDiffOn
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    {D : RealTimeInterval}
    {G : RealizedMetricFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {h : ℝ → OneFormSection (I := I) (M := M)}
    {nablaH : ℝ → TwoTensorSection (I := I) (M := M)}
    {nabla2H : ℝ → (x : M) →
      Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3 x}
    (hHeat : IsHeatOneFormOn (I := I) G h nablaH nabla2H) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => normSq0S (I := I) (G.metric p.1) p.2 2 (nablaH p.1 p.2))
      (D.regular ×ˢ (Set.univ : Set M)) := by
  refine Tensor0SBundle.normSq0S_jointContMDiffOn (fun t => G.metric t) 2 (fun t x => nablaH t x)
    D.regular_isOpen ?_ ?_
  · exact hG.frameCompSmooth
  · intro Idx _ frame u hframe m
    refine (hHeat.jointSmoothNabla frame hframe (m 0) (m 1)).congr (fun p _ => ?_)
    change nablaH p.1 p.2 (fun a : Fin 2 => frame (m a) p.2)
        = nablaH p.1 p.2 (vec2 (frame (m 0) p.2) (frame (m 1) p.2))
    congr 1
    funext a
    fin_cases a <;> simp [vec2]

end

end DifferentialGeometry.Analysis.Parabolic
