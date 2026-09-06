import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  {m n : ℕ∞ω}

theorem ContMDiffAt.partial_mfderiv_apply {Φ : P → E → M} {w : P × E → E} {p₀ : P × E}
    (hΦ : ContMDiffAt (IP.prod 𝓘(𝕜, E)) I n (Function.uncurry Φ) p₀)
    (hw : ContMDiffAt (IP.prod 𝓘(𝕜, E)) 𝓘(𝕜, E) m w p₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt (IP.prod 𝓘(𝕜, E)) I.tangent m
      (fun p : P × E => (⟨Φ p.1 p.2, mfderiv 𝓘(𝕜, E) I (Φ p.1) p.2 (w p)⟩ : TangentBundle I M))
      p₀ := by
  have harg : ContMDiffAt ((IP.prod 𝓘(𝕜, E)).prod 𝓘(𝕜, E))
      (IP.prod 𝓘(𝕜, E)) n (fun q : (P × E) × E => (q.1.1, q.2)) (p₀, p₀.2) :=
    contMDiffAt_fst.fst.prodMk contMDiffAt_snd
  have hΦ' : ContMDiffAt ((IP.prod 𝓘(𝕜, E)).prod 𝓘(𝕜, E)) I n
      (fun q : (P × E) × E => Φ q.1.1 q.2) (p₀, p₀.2) :=
    hΦ.comp (p₀, p₀.2) harg
  have hd := ContMDiffAt.mfderiv_apply (I := 𝓘(𝕜, E)) (I' := I)
    (fun (p : P × E) (v : E) => Φ p.1 v) (fun p : P × E => p.2) id w
    hΦ' contMDiffAt_snd contMDiffAt_id hw hmn
  rw [contMDiffAt_totalSpace]
  refine ⟨hΦ.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn), ?_⟩
  apply hd.congr_of_eventuallyEq
  let e := trivializationAt F (TangentSpace I) (Φ p₀.1 p₀.2)
  have hbase : ∀ᶠ p : P × E in 𝓝 p₀, Φ p.1 p.2 ∈ e.baseSet :=
    hΦ.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F (TangentSpace I) _))
  filter_upwards [hbase] with p hp
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, TangentBundle.symmL_model_space,
    ContinuousLinearMap.comp_apply]
  exact (e.continuousLinearMapAt_apply_of_mem 𝕜 hp _).symm
