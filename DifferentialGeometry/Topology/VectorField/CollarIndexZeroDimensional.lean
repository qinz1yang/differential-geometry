import DifferentialGeometry.Topology.Manifold.ZeroDimensionalProduct
import DifferentialGeometry.Topology.VectorField.CollarIndexReal
import DifferentialGeometry.Topology.VectorField.CollarIndexZeros
import DifferentialGeometry.Topology.VectorField.InteriorIndexTransport
import DifferentialGeometry.Topology.VectorField.Pushforward

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorField
open DifferentialGeometry.LocalDegree DifferentialGeometry.Manifold
variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  (J : ModelWithCorners ℝ E H)

theorem mpullback_collarExtension_zeroDimensionalProductChart
    (T : ∀ p : B, TangentSpace J p) (b : B → ℝ) (ρ : ℝ → ℝ)
    (p : B) (x : EuclideanSpace ℝ (Fin 1)) :
    _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (J.prod 𝓘(ℝ, ℝ))
      (zeroDimensionalProductChart J p) (collarExtension T b ρ) x =
      realEuclideanIsometry ((collarExtension T b ρ (p, realEuclideanIsometry.symm x)).2) := by
  have hi := isInvertible_mfderiv_partialDiffeomorph
    (zeroDimensionalProductChart J p) one_ne_zero (show x ∈ Set.univ from trivial)
  have he : collarExtension T b ρ (zeroDimensionalProductChart J p x) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (J.prod 𝓘(ℝ, ℝ))
        (zeroDimensionalProductChart J p) x
        (realEuclideanIsometry ((collarExtension T b ρ (p, realEuclideanIsometry.symm x)).2)) := by
    rw [mfderiv_zeroDimensionalProductChart]
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact (realEuclideanIsometry.symm_apply_apply _).symm
  unfold _root_.VectorField.mpullback
  exact (congrArg (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (J.prod 𝓘(ℝ, ℝ))
    (zeroDimensionalProductChart J p) x).inverse he).trans (hi.inverse_apply_self _)

variable [IsManifold J 1 B]
  {H' M : Type*} [TopologicalSpace H'] [TopologicalSpace M] [ChartedSpace H' M]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 1)) H') [IsManifold I 1 M]

theorem exists_collarPushforward_index_zeroDimensional
    (Φ : PartialDiffeomorph (J.prod 𝓘(ℝ, ℝ)) I (B × ℝ) M 1)
    {T : ∀ p : B, TangentSpace J p} {b : B → ℝ} {p : B} {t : ℝ}
    (hΦ : (p, t) ∈ Φ.source) (hT : HasContinuousIsolatedZero J T p)
    (hb : ContMDiffAt J 𝓘(ℝ, ℝ) 1 b p) (hb0 : b p ≠ 0)
    (hz : collarExtension T b collarTransition (p, t) = 0) :
    let W := _root_.VectorField.mpullback I (J.prod 𝓘(ℝ, ℝ)) Φ.symm
      (collarExtension T b collarTransition)
    ∃ (hW : HasContinuousIsolatedZero I W (Φ (p, t)))
      (hWI : I.IsInteriorPoint (Φ (p, t))),
      interiorIndex I W (Φ (p, t)) hW hWI = 1 := by
  intro W
  have hC := hT.collarExtension_of_contMDiffAt J hb hb0 hz
  have hC' : HasContinuousIsolatedZero (J.prod 𝓘(ℝ, ℝ))
      (collarExtension T b collarTransition) (Φ.symm (Φ (p, t))) :=
    (Φ.left_inv hΦ).symm ▸ hC
  have hW := hC'.mpullback I (J.prod 𝓘(ℝ, ℝ)) Φ.symm le_rfl (Φ.map_source hΦ)
  let P := zeroDimensionalProductChart J p
  let a := realEuclideanIsometry t
  have ha : a ∈ P.source := trivial
  have hPa : P a = (p, t) := Prod.ext rfl (realEuclideanIsometry.symm_apply_apply t)
  let Γ := P.trans Φ
  have hΓa : a ∈ Γ.source := by
    refine ⟨ha, ?_⟩
    change P a ∈ Φ.source
    rw [hPa]
    exact hΦ
  have hc : Γ a = Φ (p, t) := congrArg Φ hPa
  have hWI : I.IsInteriorPoint (Φ (p, t)) := hc ▸
    DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph I 1 Γ one_ne_zero hΓa
  refine ⟨hW, hWI, ?_⟩
  have hW' : HasContinuousIsolatedZero I W (Γ a) := hc.symm ▸ hW
  have hΓ := hW'.model_pullback I Γ le_rfl hΓa
  obtain ⟨R, hR⟩ := realIsolatedZero_collarExtension_normal hb0 hz
  have heq : _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) I Γ W =ᶠ[𝓝 a]
      (fun v => realEuclideanIsometry
        ((collarExtension T b collarTransition (p, realEuclideanIsometry.symm v)).2)) := by
    filter_upwards [Γ.open_source.mem_nhds hΓa] with v hv
    exact (mpullback_trans_symm_partialDiffeomorph P Φ one_ne_zero
      (collarExtension T b collarTransition) hv.1 hv.2).trans
      (mpullback_collarExtension_zeroDimensionalProductChart J T b collarTransition p v)
  have hd := (interiorIndex_eq_localDegree I Γ hΓa hW').trans
    ((euclideanLocalDegree_congr hΓ ⟨R, hR.euclidean⟩ heq).trans
      ((euclideanLocalDegree_eq_realLocalDegree hR).trans
        (realLocalDegree_collarExtension_normal hb0 hz)))
  simpa only [hc] using hd

end DifferentialGeometry.VectorField
