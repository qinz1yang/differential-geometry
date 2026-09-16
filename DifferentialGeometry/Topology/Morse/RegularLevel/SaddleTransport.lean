import DifferentialGeometry.Topology.Morse.RegularLevel.LocalTransport
import DifferentialGeometry.Topology.Morse.NormalForm.SaddleField
import DifferentialGeometry.Analysis.ODE.IntegralCurveNaturality

open Set Manifold
open scoped ContDiff
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.Morse

theorem exists_ambient_isotopy_local_level_transport_saddle
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ F H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] (hdim : Module.finrank ℝ F = 2)
    {e : M → E × ℝ} (he : IsSmoothEmbedding I 𝓘(ℝ, E × ℝ) ∞ e)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] E) {β : ℝ × ℝ → M} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hβ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ β U)
    {c s : ℝ} (hgraph : ∀ z ∈ U,
      e (β z) = (B z, c + (1 - z.1 ^ 2) * (z.2 ^ 2 + 2 * s) / 2))
    {K C O : Set M} (hK : IsCompact K)
    (hregular : ∀ x ∈ K, ¬ IsCriticalPointAt I (fun x => (e x).2) x)
    (hO : IsOpen O) (hKO : K ⊆ O) (hC : IsCompact C)
    (hCβ : C ⊆ β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0}) :
    ∃ δ > 0, ∃ N P : Set M, IsOpen N ∧ K ⊆ N ∧ IsOpen P ∧ C ⊆ P ∧
      P ⊆ β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0} ∧
      ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ t ∈ Icc (-δ) δ, ∀ x ∈ N, Φ t x ∈ O ∧ (e (Φ t x)).2 = (e x).2 + t) ∧
        (∀ t ∈ Icc (-δ) δ,
          MapsTo (Φ t) P (β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0})) ∧
        (∀ x ∈ P, IsIntegralCurveOn (fun t => B.symm (e (Φ t x)).1)
          (fun _ => saddleBandVectorField) (Icc (-δ) δ)) ∧
        ∃ A : ℝ → (E × ℝ) ≃ₘ[ℝ] (E × ℝ),
          ContDiff ℝ ∞ (fun p : ℝ × (E × ℝ) => A p.1 p.2) ∧
          ContDiff ℝ ∞ (fun p : ℝ × (E × ℝ) => (A p.1).symm p.2) ∧
          A 0 = Diffeomorph.refl 𝓘(ℝ, E × ℝ) (E × ℝ) ∞ ∧
          (∀ t ∈ Icc (-δ) δ, ∀ x, A t (e x) = e (Φ t x) ∧
            (A t).symm (e (Φ t x)) = e x) ∧
          ∃ S : Set (E × ℝ), IsCompact S ∧ ∀ t,
            EqOn (A t) id Sᶜ ∧ EqOn (A t).symm id Sᶜ := by
  let _ : FiniteDimensional ℝ F := FiniteDimensional.of_finrank_pos (by omega)
  let L : E ≃L[ℝ] (ℝ × ℝ) :=
    (B.symm.isLocalDiffeomorph 0).mfderivToContinuousLinearEquiv (by simp)
  let _ : FiniteDimensional ℝ E := FiniteDimensional.of_injective L.toLinearMap L.injective
  obtain ⟨χ, hsource, _, hχ, _, W, hW, hcoords, hdf⟩ :=
    exists_unitSpeedVectorField_on_saddle_band hdim he.contMDiff B hU hβ hgraph
  let V := β '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0}
  have hV : IsOpen V := by
    have hmodel : IsOpen {z : ℝ × ℝ | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0} :=
      hU.inter (isOpen_ne.preimage (by fun_prop))
    rw [show V = χ '' {z | z ∈ U ∧ (1 - z.1 ^ 2) * z.2 ≠ 0} by rw [hχ]]
    exact χ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hmodel
      (fun z hz => hsource.symm ▸ hz.1)
  let W' : (x : M) → TangentSpace I x := fun x => -W x
  have hW' : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, W' x⟩ : TangentBundle I M)) V :=
    hW.neg_section
  have hdf' (x : M) (hx : x ∈ V) :
      NormedSpace.fromTangentSpace ((e x).2)
        (mfderiv I 𝓘(ℝ) (fun x => (e x).2) x (W' x)) = 1 := by
    simp only [W', map_neg, hdf x hx, neg_neg]
  obtain ⟨δ, hδ, N, P, hN, hKN, hP, hCP, hPV, Φ, hΦ, hΦi, hΦ0, hheight,
      hstay, hcurve, A, hA, hAi, hA0, hAe, hsupport⟩ :=
    exists_ambient_isotopy_local_level_transport_relative he (ContinuousLinearMap.snd ℝ E ℝ)
      hK hregular hO hKO hC hV hCβ W' hW' hdf'
  refine ⟨δ, hδ, N, P, hN, hKN, hP, hCP, hPV, Φ, hΦ, hΦi, hΦ0, hheight,
    hstay, ?_, A, hA, hAi, hA0, hAe, hsupport⟩
  intro x hx
  have hG : ContMDiff I 𝓘(ℝ, ℝ × ℝ) ∞ (fun x => B.symm (e x).1) :=
    B.symm.contMDiff.comp (contDiff_fst.contMDiff.comp he.contMDiff)
  apply isMIntegralCurveOn_iff_isIntegralCurveOn.mp
  apply (hcurve x hx).map (fun t _ => hG.mdifferentiable (by simp) _)
  intro t ht
  have hc := hcoords (Φ t x) (hstay t ht hx)
  change mfderiv I 𝓘(ℝ, ℝ × ℝ) (fun x => B.symm (e x).1) (Φ t x) (-W (Φ t x)) = _
  rw [map_neg, hc]
  apply Prod.ext
  · change -(0 : ℝ) = 0
    exact neg_zero
  · change -(-((1 - (B.symm (e (Φ t x)).1).1 ^ 2) * (B.symm (e (Φ t x)).1).2)⁻¹) = _
    exact neg_neg _

end DifferentialGeometry.Topology.Morse
