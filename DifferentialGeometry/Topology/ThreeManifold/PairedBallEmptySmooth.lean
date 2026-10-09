import DifferentialGeometry.Topology.ThreeManifold.PairedBallAllSeam
import DifferentialGeometry.Topology.ThreeManifold.PairedBallEmpty
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Interior
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Sigma

set_option autoImplicit false
noncomputable section
open Set Function Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {V : Type v} {E : Type w} [IsEmpty E]
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : E3) 2)
      (flagMap N endpoint chart q '' closedBall (0 : E3) 2))
  (attachment : E → BoundaryAttachment)
  (C : ∀ v, SmoothBoundaryAtlas (𝓡 3) 3
    {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
      ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1})

theorem exists_smooth_quotient_atlas_of_isEmpty :
    let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
      (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
    ∃ Qcharts : ChartedSpace E3
      (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (attachment e) x y)),
      let _ := Qcharts
      IsManifold (𝓡 3) ∞
        (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (attachment e) x y)) ∧
      IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞
        (allCoreInclusion N endpoint chart hdisj attachment) ∧
      (∀ e, IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (allSeamChart N endpoint chart hdisj attachment e)) ∧
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3)
          (Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (attachment e) x y))
          (Σ v, (N v).Carrier) ∞,
        ∀ q, D q = quotientHomeomorphOfIsEmpty N endpoint chart hdisj attachment q := by
  let _ : ∀ v, ChartedSpace (EuclideanHalfSpace 3)
    (PuncturedFactor N endpoint chart v) := fun v => (C v).toChartedSpace
  let _ : ∀ v, IsManifold (𝓡∂ 3) ∞ (PuncturedFactor N endpoint chart v) :=
    fun v => (C v).isManifold
  let H := quotientHomeomorphOfIsEmpty N endpoint chart hdisj attachment
  let Qcharts := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) H
  let _ := Qcharts
  let _ := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) H
  refine ⟨Qcharts, inferInstance, ?_, fun e => isEmptyElim e,
    DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡 3) (n := ∞) H,
    fun _ => rfl⟩
  apply isLocalDiffeomorph_pullback_of_comp H
  let f : (Σ v, PuncturedFactor N endpoint chart v) → Σ v, (N v).Carrier :=
    fun x => ⟨x.fst, x.snd.val⟩
  have hf : IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞ f := by
    apply (isLocalDiffeomorph_sigma_iff f).mpr
    intro v
    change IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞
      ((Sigma.mk (β := fun w => (N w).Carrier) v) ∘
        (Subtype.val : PuncturedFactor N endpoint chart v → (N v).Carrier))
    apply DifferentialGeometry.isLocalDiffeomorph_comp
      (isLocalDiffeomorph_sigmaMk (I := 𝓡 3) (M := fun w => (N w).Carrier) v)
    intro x
    apply (C v).isLocalDiffeomorphAt_subtype_val
    have hK : {x : (N v).Carrier | (⟨v, x⟩ : Σ v, (N v).Carrier) ∉
        ⋃ p, flagMap N endpoint chart p '' ball (0 : E3) 1} = univ := by
      ext x
      simp
    simpa only [hK, interior_univ] using (mem_univ x.val)
  change IsLocalDiffeomorph (𝓡∂ 3) (𝓡 3) ∞
    (f ∘ (Subtype.val : allCore N endpoint chart hdisj → Σ v, PuncturedFactor N endpoint chart v))
  exact DifferentialGeometry.isLocalDiffeomorph_comp hf
    (DifferentialGeometry.isLocalDiffeomorph_subtype_val (allCore N endpoint chart hdisj))

end DifferentialGeometry.Topology.PairedBallGluing
