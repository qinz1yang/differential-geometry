import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalParam
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalParamRemodel
import DifferentialGeometry.Geometry.Metric.Subbundle
import DifferentialGeometry.Bundle.SmoothSubbundle.Range

/-!
# The smoothed normal bundle `Ê = range P̂` and the binding of `ι` (lane CMS3-CARRIER, group G2b)

Design §0 decision 7 and review §11: the smooth Riemannian bundle `Ê` is the range of the smooth
projection field `P̂` of §10, built by the EXISTING `ContMDiffVectorSubbundle.range` (wrap `P̂` as a
smooth section `s ↦ (s, P̂ s)` of `Hom(B × ℝ^K, B × ℝ^K)`; `contMDiff_trivialHomSection`), with the
Euclidean fibre norm of `ℝ^K`. Its model fibre `Fin k → ℝ` is re-modelled along
`EuclideanSpace.equiv` to `ℝ^k = EuclideanSpace ℝ (Fin k)` (`NormalParamRemodel.lean`), as the frozen
LFR46 / LFR47 interfaces demand an inner-product model fibre.

`exists_soulNormalBundle` (same witness as `exists_normalParametrization`): there is a smooth
Riemannian vector bundle `V → B` with model `ℝ^(dim − d)` and a map `ιE : TotalSpace ℝ^(dim−d) V → TM`
satisfying EXACTLY the `ι`-hypotheses of LFR46 (`hι`, `hιb`, `hιlin`, `hιnorm`, `hιν`, `hιonto`),
plus the zero-section formula `ιE (s, 0) = 0_{b s}` and the relation `ιE (s, w) = ι (s, w)` with the
§10 map.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric Topology
open scoped Manifold ContDiff InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

section TrivialHom

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}

/-- A smooth endomorphism field of `ℝ^K` is a smooth section of `Hom(B × ℝ^K, B × ℝ^K)`. -/
theorem contMDiff_trivialHomSection (P : B → F →L[ℝ] F)
    (hP : ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, F →L[ℝ] F) n P) :
    ContMDiff 𝓘(ℝ, EB) (𝓘(ℝ, EB).prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun x => TotalSpace.mk' (F →L[ℝ] F) (E := fun x => Trivial B F x →L[ℝ] Trivial B F x) x
        (P x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply (hP x₀).congr_of_eventuallyEq
  filter_upwards with x
  ext v
  simp [ContinuousLinearMap.inCoordinates]

/-- The fibre coordinate of the trivial bundle is smooth. -/
theorem contMDiff_trivial_snd :
    ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) n (fun w : TotalSpace F (Trivial B F) => w.snd) :=
  fun w₀ => ((contMDiffAt_totalSpace (f := id) (x₀ := w₀) (IB := 𝓘(ℝ, EB)) (n := n)).mp
    contMDiffAt_id).2

end TrivialHom

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B] [CompactSpace B]
  [T2Space B]

variable {r : ℕ∞}

/-- **`Ê` and the binding of `ι` to the LFR46 hypotheses** (`2 ≤ r`). -/
theorem exists_soulNormalBundle
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r) {S : Set M} {d : ℕ} (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S)
    (b : B → M) (hb : ContMDiff 𝓘(ℝ, EB) I ((r - 1 : ℕ∞) : ℕ∞ω) b) (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x) :
    ∃ (V : B → Type) (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
      (_ : TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - d))) V))
      (_ : FiberBundle (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - d))) V)
      (_ : VectorBundle ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - d))) V)
      (_ : ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - d))) V 𝓘(ℝ, EB))
      (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - d))) V)
      (ιE : TotalSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - d))) V → TangentBundle I M),
      ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - d)))) I.tangent
        ((r - 1 : ℕ∞) : ℕ∞ω) ιE ∧
      (∀ z, (ιE z).proj = b z.proj) ∧
      (∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ιE ⟨s, w⟩).snd (A w)) ∧
      (∀ z, g.inner (ιE z).proj (ιE z).snd (ιE z).snd = ‖z.2‖ ^ 2) ∧
      (∀ z, ιE z ∈ normalSetFinite g S) ∧
      (∀ v ∈ normalSetFinite g S, ∃ z, ιE z = v) ∧
      (∀ s : B, ιE ⟨s, 0⟩ = (⟨b s, 0⟩ : TangentBundle I M)) := by
  classical
  obtain ⟨K, Phat, ι, -, hPhat, hPi, -, hrank, hι, hιb, hιlin, hιP, hιnor, hιonto, hι0, -, -, -⟩ :=
    exists_normalParametrization_data g hr hS b hb hbS hbinv
  set k : ℕ := Module.finrank ℝ E - d with hk
  set Sb := ContMDiffVectorSubbundle.range (I := 𝓘(ℝ, EB)) (n := ∞)
    (V₁ := Trivial B (EuclideanSpace ℝ (Fin K))) (V₂ := Trivial B (EuclideanSpace ℝ (Fin K)))
    (fun x => Phat x) (contMDiff_trivialHomSection Phat hPhat) k hrank with hSb
  let V : B → Type := fun s => Sb.fiber s
  let tOld : TopologicalSpace (TotalSpace (Fin k → ℝ) V) := Sb.totalSpaceTopology
  let fbOld : FiberBundle (Fin k → ℝ) V := Sb.fiberBundle
  have vbOld : VectorBundle ℝ (Fin k → ℝ) V := Sb.vector_bundle
  have cvbOld : ContMDiffVectorBundle ∞ (Fin k → ℝ) V 𝓘(ℝ, EB) := Sb.contMDiffVectorBundle
  let L : (Fin k → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin k) := (EuclideanSpace.equiv (Fin k) ℝ).symm
  let tE : TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin k)) V) :=
    remodelTopology (Fin k → ℝ) (EuclideanSpace ℝ (Fin k)) V
  have hσ : IsInducing (remodelEquiv (Fin k → ℝ) (EuclideanSpace ℝ (Fin k)) V) :=
    isInducing_remodelEquiv
  let fbE : FiberBundle (EuclideanSpace ℝ (Fin k)) V := remodelFiberBundle L hσ
  have vbE : VectorBundle ℝ (EuclideanSpace ℝ (Fin k)) V := remodelVectorBundle L hσ
  have cvbE : ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin k)) V 𝓘(ℝ, EB) :=
    remodelContMDiffVectorBundle (IB := 𝓘(ℝ, EB)) L hσ
  -- the inclusion of the re-modelled bundle into `B × ℝ^K`
  have hincl : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin k)))
      (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K))) ∞
      (fun z : TotalSpace (EuclideanSpace ℝ (Fin k)) V =>
        (⟨z.proj, (z.snd : EuclideanSpace ℝ (Fin K))⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin K)) (Trivial B (EuclideanSpace ℝ (Fin K))))) :=
    by
      let _ := Sb.totalSpaceTopology
      let _ := Sb.fiberBundle
      let _ := Sb.vector_bundle
      let _ := Sb.contMDiffVectorBundle
      exact Sb.contMDiff_subtypeVal.comp (contMDiff_remodelEquiv (IB := 𝓘(ℝ, EB)) L hσ)
  have rbE : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin k)) V := by
    obtain ⟨g₀, hg₀, hinner⟩ := IsContMDiffRiemannianBundle.exists_contMDiff (IB := 𝓘(ℝ, EB))
      (n := ∞) (F := EuclideanSpace ℝ (Fin K)) (E := Trivial B (EuclideanSpace ℝ (Fin K)))
    have hinc := ContMDiff.clm_bundle_of_map (φ := fun x => (Sb.fiber x).subtypeL) hincl
    refine ⟨fun x => (g₀ x).bilinearComp (Sb.fiber x).subtypeL (Sb.fiber x).subtypeL,
      hg₀.clm_bundle_bilinearComp hinc hinc, ?_⟩
    intro x v w
    exact hinner x v w
  refine ⟨V, inferInstance, inferInstance, tE, fbE, vbE, cvbE, rbE,
    fun z => ι (z.proj, (z.snd : EuclideanSpace ℝ (Fin K))), ?_, fun z => hιb _ _, ?_, ?_, ?_, ?_,
    fun s => hι0 s⟩
  · have hprod : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin k)))
        (𝓘(ℝ, EB).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin K))) ∞
        (fun z : TotalSpace (EuclideanSpace ℝ (Fin k)) V =>
          (z.proj, (z.snd : EuclideanSpace ℝ (Fin K)))) :=
      (Bundle.contMDiff_proj V).prodMk (contMDiff_trivial_snd.comp hincl)
    exact hι.comp (hprod.of_le (WithTop.coe_le_coe.mpr le_top))
  · intro s
    obtain ⟨A, hA⟩ := hιlin s
    exact ⟨A.comp (Sb.fiber s).subtypeL, fun w => hA _⟩
  · rintro ⟨s, w⟩
    have hw : Phat s (w : EuclideanSpace ℝ (Fin K)) = w := by
      obtain ⟨u, hu⟩ := w.2
      rw [← hu]
      exact congrArg (fun T => T u) (hPi s)
    exact (hιnor s _ hw).2
  · rintro ⟨s, w⟩
    have hw : Phat s (w : EuclideanSpace ℝ (Fin K)) = w := by
      obtain ⟨u, hu⟩ := w.2
      rw [← hu]
      exact congrArg (fun T => T u) (hPi s)
    exact (hιnor s _ hw).1
  · intro v hv
    obtain ⟨s, w, hw, rfl⟩ := hιonto v hv
    exact ⟨⟨s, ⟨w, ⟨w, hw⟩⟩⟩, rfl⟩

end DifferentialGeometry.Geometry.FiniteSoul
