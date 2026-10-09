import DifferentialGeometry.Topology.Manifold.SmoothChartBaseManifoldOBD
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkOfStageSrc74

/-!
# A smooth stage over `W` with embedded base inclusion (lane S-BD2c, suffix `_OBD`)

`exists_stageProj_of_charts_smooth_OBD` (G7e) with the stronger conclusion that the identification
`ι` of the base into the ambient space is a smooth EMBEDDING
(`IsSmoothEmbedding (𝓡 k) 𝓘(ℝ, H) ∞ ι`: smooth, injective differential, topological embedding):
the chart transport of the base manifold structure (circle trivializations, rim base, face
functions along the base) needs it. Same proof (the differential of the inclusion of the chart
manifold `B ⊆ H` is injective by `exists_smoothChartedBase_OBD`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold Topology
open scoped ContDiff Manifold Topology
open DifferentialGeometry DifferentialGeometry.Topology.Manifold
open GC.Endpoint GC.GraphManifold GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

/-- **A stage over `W` from embedded parametrizations of the base.** -/
theorem exists_stageProj_of_charts_embedded_OBD {W : CompactCarrier.{0}} {k : ℕ}
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (f : W.Carrier → H) {X : Set W.Carrier} (hX : IsOpen X) (hXi : X ⊆ (W.interior : Set W.Carrier))
    (B : Set H) (hf : ∀ p ∈ X, ContMDiffAt W.model 𝓘(ℝ, H) ∞ f p) (hmaps : ∀ p ∈ X, f p ∈ B)
    (hchart : ∀ y ∈ B, ∃ (σ : EuclideanSpace ℝ (Fin k) → H) (O : Set H), σ 0 = y ∧
      ContDiff ℝ ∞ σ ∧ IsEmbedding σ ∧ (∀ x, Injective (fderiv ℝ σ x)) ∧ IsOpen O ∧
      range σ = B ∩ O)
    (hrank : ∀ p ∈ X, Module.finrank ℝ (LinearMap.range
      ((mvfderiv W.model f p : TangentSpace W.model p →L[ℝ] H) :
        TangentSpace W.model p →ₗ[ℝ] H)) = k) :
    ∃ (Q : StageProj74 W k) (ι : Q.Base → H), StageIdentSrc_LND74 Q f ι X ∧ range ι = B ∧
      IsSmoothEmbedding (𝓡 k) 𝓘(ℝ, H) ∞ ι := by
  obtain ⟨cs, hM, hval, himm, hinto⟩ := exists_smoothChartedBase_OBD (E := EuclideanSpace ℝ
      (Fin k)) B hchart
  let par : TopologicalSpace.Opens W.Carrier := ⟨X, hX⟩
  have hsm : ContMDiff W.model 𝓘(ℝ, H) ∞ (fun z : par => f z) := by
    intro z
    exact (hf z z.2).comp z ((contMDiff_subtype_val (I := W.model) (U := par)) z)
  let pr : par → B := fun z => ⟨f z, hmaps z z.2⟩
  have hprsm : ContMDiff W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ pr := hinto W.model pr hsm
  have hsubmer : ∀ x : par, Surjective (mfderiv W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) pr x) := by
    intro x
    have hpd : MDifferentiableAt W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) pr x :=
      (hprsm x).mdifferentiableAt (by simp)
    have hvd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, H) (Subtype.val : B → H)
        (pr x) := (hval (pr x)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp x hvd hpd
    have hfd : MDifferentiableAt W.model 𝓘(ℝ, H) f (x : W.Carrier) :=
      (hf x x.2).mdifferentiableAt (by simp)
    have hvv : MDifferentiableAt W.model W.model (Subtype.val : par → W.Carrier) x :=
      ((contMDiff_subtype_val (I := W.model) (U := par)) x).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp2 := mfderiv_comp x hfd hvv
    have hvp : (Subtype.val ∘ pr : par → H) = f ∘ (Subtype.val : par → W.Carrier) := rfl
    rw [hvp, hcomp2, mfderiv_subtype_val (I := W.model) par x] at hcomp
    have hrk := hrank x x.2
    let D : TangentSpace W.model x →L[ℝ] EuclideanSpace ℝ (Fin k) :=
      mfderiv W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) pr x
    let Dv : EuclideanSpace ℝ (Fin k) →L[ℝ] H :=
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 𝓘(ℝ, H) (Subtype.val : B → H) (pr x)
    let A : TangentSpace W.model (x : W.Carrier) →L[ℝ] H :=
      mfderiv W.model 𝓘(ℝ, H) f (x : W.Carrier)
    have hmv : mvfderiv W.model f (x : W.Carrier) = A := rfl
    rw [hmv] at hrk
    have hAeq : A = Dv.comp D := hcomp
    have h1 : LinearMap.range A.toLinearMap = Submodule.map Dv.toLinearMap
        (LinearMap.range D.toLinearMap) := by
      have hAl : A.toLinearMap = Dv.toLinearMap.comp D.toLinearMap := by rw [hAeq]; rfl
      rw [hAl]
      exact LinearMap.range_comp _ _
    have h2 := (Submodule.equivMapOfInjective Dv.toLinearMap (himm (pr x))
      (LinearMap.range D.toLinearMap)).finrank_eq
    rw [← h1, hrk] at h2
    have h3 : LinearMap.range D.toLinearMap = ⊤ :=
      Submodule.eq_top_of_finrank_eq (h2.trans finrank_euclideanSpace_fin.symm)
    exact LinearMap.range_eq_top.1 h3
  let Q : StageProj74 W k :=
    { Base := B
      parent := par
      parent_interior := hXi
      proj := ⟨pr, hprsm.continuous⟩
      proj_smooth := hprsm
      proj_submersion := hsubmer }
  refine ⟨Q, Subtype.val, ?_, ?_, ?_⟩
  · exact ⟨IsEmbedding.subtypeVal, fun z => rfl, rfl⟩
  · exact Subtype.range_coe
  · refine ⟨?_, IsEmbedding.subtypeVal⟩
    exact isImmersion_of_injective_mfderiv (by simp) hval himm

end DifferentialGeometry.Geometry.Collapse
