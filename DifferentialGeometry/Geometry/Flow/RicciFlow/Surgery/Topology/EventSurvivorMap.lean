import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedMaps
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_isometric_survivor_map
    (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old)) :
    ∃ F : W → Q.Carrier, ContMDiff ThreeModel ThreeModel ∞ F ∧
      Function.Injective F ∧ IsLocalDiffeomorph ThreeModel ThreeModel ∞ F ∧
      (∀ x : W, ∃ z : E.old, E.oldTerminal z = x.val ∧ F x = E.oldOutput z ∧
        E.RegularCrossing x.val.val (F x)) ∧
      (∀ z : E.old, ∀ hz : E.oldTerminal z ∈ W, F ⟨E.oldTerminal z, hz⟩ = E.oldOutput z) ∧
      ∀ (x : W) (v w : TangentSpace ThreeModel x),
        E.outputMetric.inner (F x) (mfderiv ThreeModel ThreeModel F x v)
          (mfderiv ThreeModel ThreeModel F x w) =
          (E.terminal.metric.restrictOpen W).inner x v w := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  have hsub : range (Subtype.val : W → E.incoming.terminalRegularOpen) ⊆ range E.oldTerminal := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz, _, _⟩ := E.exists_oldTerminal_eq_of_mem_interior_old x.val (hW x.val x.property)
    exact ⟨z, hz⟩
  let σ : W → E.old := E.oldTerminal_isSmoothEmbedding.lift Subtype.val hsub
  have hσ : ContMDiff ThreeModel (𝓡∂ 3) ∞ σ :=
    E.oldTerminal_isSmoothEmbedding.contMDiff_lift (contMDiff_subtype_val (U := W)) hsub
  have hσterm (x : W) : E.oldTerminal (σ x) = x.val :=
    E.oldTerminal_isSmoothEmbedding.comp_lift hsub x
  let F : W → Q.Carrier := E.oldOutput ∘ σ
  have hF : ContMDiff ThreeModel ThreeModel ∞ F := E.contMDiff_oldOutput.comp hσ
  have hinj : Function.Injective F := by
    intro x y hxy
    have hσeq := E.oldOutput_injective hxy
    apply Subtype.ext
    rw [← hσterm x, ← hσterm y, hσeq]
  have hmetric (x : W) (v w : TangentSpace ThreeModel x) :
      E.outputMetric.inner (F x) (mfderiv ThreeModel ThreeModel F x v)
        (mfderiv ThreeModel ThreeModel F x w) =
        (E.terminal.metric.restrictOpen W).inner x v w := by
    have hO := mfderiv_comp x (E.contMDiff_oldOutput.mdifferentiableAt (by simp))
      (hσ.mdifferentiableAt (by simp))
    have hT := mfderiv_comp x
      (E.oldTerminal_isSmoothEmbedding.contMDiff.mdifferentiableAt (by simp))
      (hσ.mdifferentiableAt (by simp))
    have hfT : E.oldTerminal ∘ σ = Subtype.val := funext hσterm
    rw [hfT, DifferentialGeometry.mfderiv_subtype_val] at hT
    have hv : mfderiv (𝓡∂ 3) ThreeModel E.oldTerminal (σ x)
        (mfderiv ThreeModel (𝓡∂ 3) σ x v) = v :=
      (congrArg (fun A : ThreeSpace →L[ℝ] ThreeSpace => A v) hT).symm
    have hw : mfderiv (𝓡∂ 3) ThreeModel E.oldTerminal (σ x)
        (mfderiv ThreeModel (𝓡∂ 3) σ x w) = w :=
      (congrArg (fun A : ThreeSpace →L[ℝ] ThreeSpace => A w) hT).symm
    dsimp only [F]
    rw [hO]
    change E.outputMetric.inner (E.oldOutput (σ x))
      (mfderiv (𝓡∂ 3) ThreeModel E.oldOutput (σ x) (mfderiv ThreeModel (𝓡∂ 3) σ x v))
      (mfderiv (𝓡∂ 3) ThreeModel E.oldOutput (σ x) (mfderiv ThreeModel (𝓡∂ 3) σ x w)) = _
    rw [← E.old_metric_eq, hv, hw, hσterm]
    rfl
  have himm (x : W) : Function.Injective (mfderiv ThreeModel ThreeModel F x) := by
    intro v w hvw
    have hz : mfderiv ThreeModel ThreeModel F x (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have heq := hmetric x (v - w) (v - w)
    rw [hz, map_zero] at heq
    by_contra hne
    exact (ne_of_gt ((E.terminal.metric.restrictOpen W).pos x (v - w)
      (sub_ne_zero.mpr hne))) heq.symm
  have hloc := DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    F hF himm rfl
  refine ⟨F, hF, hinj, hloc, ?_, ?_, hmetric⟩
  · intro x
    obtain ⟨z, hz, hi, hc⟩ := E.exists_oldTerminal_eq_of_mem_interior_old x.val (hW x.val x.property)
    have heq : σ x = z := E.oldTerminal_isSmoothEmbedding.isEmbedding.injective
      ((hσterm x).trans hz.symm)
    refine ⟨z, hz, ?_, ?_⟩
    · exact congrArg E.oldOutput heq
    · simpa only [F, Function.comp_apply, heq] using hc
  · intro z hz
    apply congrArg E.oldOutput
    exact E.oldTerminal_isSmoothEmbedding.isEmbedding.injective (hσterm ⟨E.oldTerminal z, hz⟩)

theorem exists_survivor_partialDiffeomorph
    (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen) (x₀ : W)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old)) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel
        E.incoming.terminalRegularOpen Q.Carrier ∞,
      F.source = W ∧
      (∀ x ∈ W, E.RegularCrossing x.val (F x)) ∧
      (∀ z : E.old, E.oldTerminal z ∈ W → F (E.oldTerminal z) = E.oldOutput z) ∧
      ∀ x ∈ W, ∀ v w : TangentSpace ThreeModel x,
        E.outputMetric.inner (F x) (mfderiv ThreeModel ThreeModel (F : _ → _) x v)
          (mfderiv ThreeModel ThreeModel (F : _ → _) x w) =
          E.terminal.metric.inner x v w := by
  obtain ⟨f, hf, hinj, hloc, hcross, hold, hmetric⟩ := E.exists_isometric_survivor_map W hW
  let V := hloc.image
  let e : W ≃ₘ⟮ThreeModel, ThreeModel⟯ V :=
    DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage f hloc hinj
  let iW := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel W ⟨x₀⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V ⟨e x₀⟩
  let F := (iW.symm.trans e.toPartialDiffeomorph).trans iV
  have hiW : iW.target = (W : Set E.incoming.terminalRegularOpen) :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target _ _ _
  have hsource : F.source = (W : Set E.incoming.terminalRegularOpen) := by
    ext x
    change ((x ∈ iW.target ∧ iW.symm x ∈ (univ : Set W)) ∧
      e (iW.symm x) ∈ (univ : Set V)) ↔ x ∈ W
    simp only [mem_univ, and_true, hiW]
    rfl
  have happ (x : E.incoming.terminalRegularOpen) (hx : x ∈ W) : F x = f ⟨x, hx⟩ := by
    have hi : iW.symm x = ⟨x, hx⟩ :=
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply _ _ _ hx
    change (e (iW.symm x) : Q.Carrier) = f ⟨x, hx⟩
    rw [hi]
    rfl
  have hrest : (fun x : W => F x.val) = f := funext fun x => happ x.val x.property
  have hd (x : W) : mfderiv ThreeModel ThreeModel (F : _ → _) x.val =
      mfderiv ThreeModel ThreeModel f x := by
    rw [← DifferentialGeometry.mfderiv_restrict_open (F : _ → _) W x, hrest]
  refine ⟨F, hsource, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, _, hz, hc⟩ := hcross ⟨x, hx⟩
    simpa only [happ x hx] using hc
  · intro z hz
    rw [happ _ hz]
    exact hold z hz
  · intro x hx v w
    rw [happ x hx, hd ⟨x, hx⟩]
    exact hmetric ⟨x, hx⟩ v w


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
