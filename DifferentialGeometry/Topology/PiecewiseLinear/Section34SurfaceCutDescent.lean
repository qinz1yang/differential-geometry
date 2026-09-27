import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCutTrace
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceTraceReduction
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SupportedSurfaceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SurfaceGeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_supported_surface_nonbounding_disk
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (D : Geometry.SimplicialComplex ℝ E)
    (S K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite D.faces] [Finite S.faces] [Finite K.faces] [Finite L.faces]
    (hD : IsPLBall 2 D.space) (hS : IsCombinatorialManifoldWithBoundary 3 S)
    (hK : IsCombinatorialManifold 2 K) (hL : IsCombinatorialManifold 2 L)
    (hconn : IsConnected K.space) (hKS : K.space ⊆ interior S.space)
    (hgen : CarriesFundamentalGroupOnto K.space S.space)
    {f : E × ℝ → EuclideanSpace ℝ (Fin 3)} (hf : IsCylindricalDiagram f D.space S.space)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    (hLspace : L.space = frontier (f '' (D.space ×ˢ Icc (0 : ℝ) (1 / 2)))) :
    ∃ (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (Q : Set (EuclideanSpace ℝ (Fin 3))) (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn Φ univ univ ∧ EqOn Φ id (interior S.space)ᶜ ∧
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q ∧ Q ⊆ interior S.space ∧
      Q ∩ Φ '' K.space = q '' stdSimplexBoundary 2 ∧
      ¬ ∃ (B : Set (EuclideanSpace ℝ (Fin 3)))
        (b : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn b (stdSimplex ℝ (Fin 3)) B ∧ B ⊆ Φ '' K.space ∧
          b '' stdSimplexBoundary 2 = q '' stdSimplexBoundary 2 := by
  classical
  let P (m : ℕ) : Prop :=
    ∃ (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (N : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (J : Fin m → Set (EuclideanSpace ℝ (Fin 3))),
      N.faces.Finite ∧ IsPLHomeomorphOn Φ univ univ ∧
      EqOn Φ id (interior S.space)ᶜ ∧ N.space = Φ '' K.space ∧
      (∀ i, IsPLSphere 1 (J i)) ∧ (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      N.space ∩ L.space = ⋃ i, J i
  have hex : ∃ m, P m := by
    obtain ⟨H, N, m, J, hH, hfix, -, hNfin, -, hNspace, -, -, hJ, hdis, htrace⟩ :=
      hK.exists_relative_general_position_circles K L hL isOpen_interior hKS
        (ε := 1) zero_lt_one
    exact ⟨m, H, N, J, hNfin, hH, hfix, hNspace, hJ, hdis, htrace⟩
  obtain ⟨Φ, N, J, hNfin, hΦ, hfix, hNspace, hJ, hdis, htrace⟩ := Nat.find_spec hex
  let _ : Finite N.faces := hNfin.to_subtype
  obtain ⟨hN, hNconn, hNcpt, hNS, hNgen, -, -⟩ :=
    hK.supported_image_preserving_carrier S K N hconn hKS hgen hΦ hfix hNspace
  have htrace' : N.space ∩ frontier (f '' (D.space ×ˢ Icc (0 : ℝ) (1 / 2))) = ⋃ i, J i :=
    hLspace ▸ htrace
  obtain ⟨i, Q, q, hq, hQS, hqJ, hQN, -⟩ := hf.exists_innermost_cut_disk_of_carrier
    D S hD hS hends hNcpt hNconn.nonempty hNS hNgen hJ hdis htrace'
  have hQL : Q ⊆ L.space ∩ interior S.space := hLspace.symm ▸ hQS
  have hnot : ¬ ∃ (B : Set (EuclideanSpace ℝ (Fin 3)))
      (b : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn b (stdSimplex ℝ (Fin 3)) B ∧ B ⊆ N.space ∧
        b '' stdSimplexBoundary 2 = q '' stdSimplexBoundary 2 := by
    rintro ⟨B, b, hb, hBN, hbq⟩
    obtain ⟨Ψ, I, hΨ, hΨfix, hcard, hnew⟩ :=
      exists_strict_surface_trace_reduction_of_inessential_disk S N L hS
        (hf.isTopologicalSolidTorus_of_eq_ends hD hends) hN hL hNconn hNS hNgen
        hJ hdis htrace i hq hb hqJ (hbq.trans hqJ) hQL hBN hQN
    obtain ⟨N', hN'fin, hN'space, -⟩ :=
      hN.exists_supported_image_preserving_carrier S N hNconn hNS hNgen hΨ hΨfix
    obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin I
    have hm : m < Nat.find hex := by
      have heq := Nat.card_congr e
      simpa only [Nat.card_fin, heq] using hcard
    apply Nat.find_min hex hm
    refine ⟨Ψ ∘ Φ, N', fun j => J (e.symm j).1, hN'fin, hΦ.trans hΨ, ?_, ?_,
      fun j => hJ (e.symm j).1, ?_, ?_⟩
    · intro x hx
      change Ψ (Φ x) = x
      rw [hfix hx]
      exact hΨfix hx
    · rw [image_comp, ← hNspace]
      exact hN'space
    · intro j k hjk
      exact hdis (fun heq => hjk (e.symm.injective (Subtype.ext heq)))
    · rw [hN'space, hnew]
      exact (e.symm.surjective.iUnion_comp (fun j : I => J j.1)).symm
  refine ⟨Φ, Q, q, hΦ, hfix, hq, hQS.trans inter_subset_right, ?_, ?_⟩
  · rw [← hNspace, hQN, hqJ]
  · rwa [← hNspace]

end DifferentialGeometry.Topology.PiecewiseLinear
