import DifferentialGeometry.Topology.Ehresmann.FaceTransportNeighborhoods
import DifferentialGeometry.Topology.Ehresmann.FaceTransportField
import DifferentialGeometry.Topology.Ehresmann.FaceTransportInvariance
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
  [I.Boundaryless] [T2Space Y] [SigmaCompactSpace Y]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ Y] [I.Boundaryless] [T2Space Y] [SigmaCompactSpace Y] in
private theorem hasFDerivAt_time_comp_of_total_zero
    (g : Y × ℝ → F) (hg : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ g)
    (γ : ℝ → Y) (t : ℝ) (v : TangentSpace I (γ t))
    (hγ : HasMFDerivAt 𝓘(ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hz : mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) g (γ t, t) (v, 1) = 0) :
    HasFDerivAt (fun u => g (γ u, u)) (0 : ℝ →L[ℝ] F) t := by
  have hq : HasMFDerivAt 𝓘(ℝ) (I.prod 𝓘(ℝ)) (fun u => (γ u, u)) t
      (((1 : ℝ →L[ℝ] ℝ).smulRight v).prod (1 : ℝ →L[ℝ] ℝ)) :=
    hγ.prodMk (hasMFDerivAt_id (I := 𝓘(ℝ)) (x := t))
  have hdg : HasMFDerivAt (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) g (γ t, t)
      (mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) g (γ t, t)) :=
    ((hg (γ t, t)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hc := hdg.comp (f := fun u => (γ u, u)) t hq
  let L : E × ℝ →L[ℝ] F := mfderiv (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) g (γ t, t)
  let w : E := v
  have hz' : L (w, 1) = (0 : F) := hz
  have heq : L.comp (((1 : ℝ →L[ℝ] ℝ).smulRight w).prod (1 : ℝ →L[ℝ] ℝ)) = 0 := by
    apply ContinuousLinearMap.ext
    intro r
    change L (r • w, r) = 0
    have hp : (r • w, r) = r • (w, (1 : ℝ)) := by
      apply Prod.ext
      · rfl
      · change r = r * 1
        exact (mul_one r).symm
    rw [hp, map_smul]
    rw [hz', smul_zero]
  have hc' : HasFDerivAt (fun u => g (γ u, u))
      (L.comp (((1 : ℝ →L[ℝ] ℝ).smulRight w).prod (1 : ℝ →L[ℝ] ℝ))) t := hc.hasFDerivAt
  rw [heq] at hc'
  exact hc'

/-- A compact trace, including its face, has a genuine compactly supported ambient transport. -/
theorem exists_diffeomorph_face_of_compact_transport
    (h : Y × ℝ → F) (T : Y × ℝ → ℝ)
    (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ, F) ∞ h)
    (hT : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ T) (a : F) (c : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hreg : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c + ε →
      Surjective (mfderiv I 𝓘(ℝ, F) (fun z => h (z, τ)) y))
    (hface : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → |T (y, τ) - c| < ε →
      Surjective (mfderiv I 𝓘(ℝ, F × ℝ) (fun z => (h (z, τ), T (z, τ))) y))
    {Q : Set Y} (hQ : IsCompact Q)
    (hloc : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ y, h (y, τ) = a → T (y, τ) ≤ c + ε → y ∈ Q) :
    ∃ Ψ : Y ≃ₘ⟮I, I⟯ Y,
      (∃ K : Set Y, IsCompact K ∧ ∀ y ∉ K, Ψ y = y) ∧
      Ψ '' {y | h (y, 0) = a ∧ T (y, 0) ≤ c} = {y | h (y, 1) = a ∧ T (y, 1) ≤ c} ∧
      Ψ '' {y | h (y, 0) = a ∧ T (y, 0) = c} = {y | h (y, 1) = a ∧ T (y, 1) = c} := by
  obtain ⟨SA, SB, K, hSA, hSB, hK, hASA, hBSB, hRA, hRB, hSK⟩ :=
    exists_compact_faceTrace_rankNeighborhoods h T hh hT a c ε hε hreg hface hQ hloc
  obtain ⟨X, hX, hzero, hXA, hXB⟩ :=
    exists_compactSupport_faceTransportField h T hh hT hSA hSB hK hSK hRA hRB
  have hsp : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  obtain ⟨Ψ, hself, hcomp, hout, hflow⟩ :=
    exists_compactSupport_ambientTransport X hX hsp hzero
  have hpres : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y,
      (h (y, s) = a ∧ T (y, s) ≤ c → ∀ t ∈ Icc (0 : ℝ) 1,
        h (Ψ s t y, t) = a ∧ T (Ψ s t y, t) ≤ c) ∧
      (h (y, s) = a ∧ T (y, s) = c → ∀ t ∈ Icc (0 : ℝ) 1,
        h (Ψ s t y, t) = a ∧ T (Ψ s t y, t) = c) := by
    intro s hs y
    let γ : ℝ → Y := fun t => Ψ s t y
    let q : ℝ → Y × ℝ := fun t => (γ t, t)
    have hγc : Continuous γ := continuous_iff_continuousAt.mpr
      (fun t => (hflow s t y).continuousAt)
    have hqc : Continuous q := hγc.prodMk continuous_id
    have hInv := face_invariant_on_Icc_of_neighborhood_derivatives
      (fun t => h (q t)) (fun t => T (q t)) (hh.continuous.comp hqc) (hT.continuous.comp hqc)
      a c (isOpen_interior.preimage hqc) (isOpen_interior.preimage hqc)
      (fun t ht hta htc => hASA ⟨ht, hta, htc⟩)
      (fun t ht hta htc => hBSB ⟨ht, hta, htc⟩)
      (fun t _ht htu => hasFDerivAt_time_comp_of_total_zero h hh γ t
        (X t (γ t)) (hflow s t y) (hXA (q t) (interior_subset htu)))
      (fun t _ht htv => by
        have hd := hasFDerivAt_time_comp_of_total_zero T hT γ t
          (X t (γ t)) (hflow s t y) (hXB (q t) (interior_subset htv)).2
        simpa only [zero_apply] using hd.hasDerivAt) hs
    simpa only [q, γ, hself] using hInv
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨Ψ 0 1, ⟨Prod.fst '' K, hsp, fun y hy => hout 0 1 y hy⟩, ?_, ?_⟩
  · apply subset_antisymm
    · rintro _z ⟨y, hy, rfl⟩
      exact (hpres 0 h0 y).1 hy 1 h1
    · intro z hz
      refine ⟨Ψ 1 0 z, (hpres 1 h1 z).1 hz 0 h0, ?_⟩
      exact (hcomp 1 0 1 z).trans (hself 1 z)
  · apply subset_antisymm
    · rintro _z ⟨y, hy, rfl⟩
      exact (hpres 0 h0 y).2 hy 1 h1
    · intro z hz
      refine ⟨Ψ 1 0 z, (hpres 1 h1 z).2 hz 0 h0, ?_⟩
      exact (hcomp 1 0 1 z).trans (hself 1 z)

end DifferentialGeometry.Topology.Ehresmann
