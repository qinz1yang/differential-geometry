import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckSupported
import DifferentialGeometry.Topology.Manifold.CylinderCollar.SphereMatching

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology.Manifold

universe u

theorem exists_horn_neck_collar_matching_of_deep_coordinates :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
          {δ₀ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ₀ k),
          δ₀ ≤ ε → ⌈ε⁻¹⌉₊ ≤ k →
          ∀ Θ : neckCentralOpen δ₀ → positiveHornDomain,
            IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ →
            (∀ z, P.horn c e (Θ z).val =
              N.chart (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ₀) z)) →
            ∀ {ρ δ : ℝ}, 0 ≤ ρ → 0 < δ → δ⁻¹ + 1 < δ₀⁻¹ →
              (∀ z, ρ + δ⁻¹ + 3 < (Θ z).val.2) →
              ∃ a : ℝ, ρ + δ⁻¹ < a ∧
                ∃ (β : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2) (σ : ℝ),
                  (β = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨
                    β = sphereAntipodalDiffeomorph (n := 2)) ∧
                  (σ = 1 ∨ σ = -1) ∧
                  ∃ F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder,
                    (∀ (q : Sphere 2) (s : ℝ), |s| ≤ δ⁻¹ →
                      ∃ hq : (β q,σ*s) ∈ neckBuffer δ₀,
                        0 < (F (q,a+s)).2 ∧
                        P.horn c e (F (q,a+s)) = N.chart ⟨(β q,σ*s),hq⟩) ∧
                    ∃ K : Set NeckCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioi ρ ∧
                      EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  obtain ⟨eta,heta,hmatch⟩ := exists_horn_neck_supported_sphere_matching_tolerance
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε c e δ₀ k N hδε hk Θ hΘ hmap ρ δ hρ hδpos hfit hdepth
  let r := δ⁻¹
  let R := r + 1 / 2
  let a := ρ + R + 1
  let b := a + 1
  have hr : 0 < r := inv_pos.mpr hδpos
  have hrR : r < R := by dsimp only [R]; linarith
  have ha : 0 < a := by dsimp only [a]; linarith
  have hρa : ρ + R < a := by dsimp only [a]; linarith
  have hab : a < b := by dsimp only [b]; linarith
  have hbdepth : b < ρ + δ⁻¹ + 3 := by dsimp only [b,a,R,r]; linarith
  obtain ⟨F₀,η,hzero,K₀,hK₀,hK₀ρ,hfix₀,hfixi₀⟩ :=
    hmatch P hε c e N hδε hk Θ hΘ hmap (ρ := ρ) ha (by linarith) hab
      (fun z => hbdepth.trans (hdepth z))
  have hsource : univ ×ˢ Icc (-R) R ⊆ (neckCentralOpen δ₀ : Set NeckCylinder) := by
    intro q hq
    have hR : R < δ₀⁻¹ := by dsimp only [R,r]; linarith
    exact ⟨mem_univ _,by linarith [hq.2.1],by linarith [hq.2.2]⟩
  have hz (q : Sphere 2) : (q,(0 : ℝ)) ∈ neckCentralOpen δ₀ :=
    ⟨mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩
  let f : neckCentralOpen δ₀ → NeckCylinder := fun q => (Θ q).val
  have hf : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ f :=
    isSmoothEmbedding_fromOpen NeckCylinderModel NeckCylinderModel positiveHornDomain Θ hΘ
  have hdepth' : ∀ q : neckCentralOpen δ₀, q.val ∈ univ ×ˢ Icc (-R) R → ρ < (f q).2 := by
    intro q _
    exact lt_trans (by change ρ < ρ + r + 3; linarith) (hdepth q)
  obtain ⟨β,σ,hβ,hσ,F,hF,K,hK,hKρ,hfix,hfixi⟩ :=
    exists_reflected_supported_collar_matching_of_embedding (neckCentralOpen δ₀) f hf F₀ η
      hr hrR hρa hsource hz hzero hdepth' K₀ hK₀ hK₀ρ hfix₀
  refine ⟨a,by change ρ + r < a; linarith,β,σ,hβ,hσ,F,?_,K,hK,hKρ,hfix,hfixi⟩
  intro q s hs
  obtain ⟨hq,heq⟩ := hF (q,s) hs
  refine ⟨neckCentralOpen_le_buffer δ₀ hq,?_,?_⟩
  · rw [heq]
    exact (Θ ⟨(β q,σ*s),hq⟩).property.2
  · rw [heq]
    exact hmap ⟨(β q,σ*s),hq⟩



theorem exists_deep_horn_neck_collar_matching_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (_ : c ∈ P.component)
          (e : P.hornIndex c) (ρ : ℝ) {δ : ℝ}, 0 < δ →
          ∃ a Q : ℝ, ρ + δ⁻¹ < a ∧ 0 < Q ∧
            ∀ {δ₀ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ₀ k),
              δ₀ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k →
              N.center ∈ TerminalCorePresentation.hornHalfRange P c e → Q < N.scale →
              δ⁻¹ + 1 < δ₀⁻¹ →
              ∃ (β : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2) (σ : ℝ),
                (β = Diffeomorph.refl (𝓡 2) (Sphere 2) ∞ ∨ β = sphereAntipodalDiffeomorph (n :=
                  2)) ∧
                (σ = 1 ∨ σ = -1) ∧
                ∃ F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder,
                  (∀ (q : Sphere 2) (s : ℝ), |s| ≤ δ⁻¹ →
                    ∃ hq : (β q,σ*s) ∈ neckBuffer δ₀,
                      0 < (F (q,a+s)).2 ∧
                      P.horn c e (F (q,a+s)) = N.chart ⟨(β q,σ*s),hq⟩) ∧
                  ∃ K : Set NeckCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioi ρ ∧
                    EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  obtain ⟨eta,heta,hmatch⟩ := exists_deep_horn_neck_supported_sphere_matching_tolerance
  refine ⟨eta,heta,?_⟩
  intro D ε Λ P hε c hc e ρ δ hδpos
  let r := δ⁻¹
  let R := r+1/2
  let a := max ρ 0+R+1
  let b := a+1
  have hr : 0 < r := inv_pos.mpr hδpos
  have hrR : r < R := by dsimp only [R]; linarith
  have ha : 0 < a := by dsimp only [a]; linarith [le_max_right ρ 0]
  have hρa : ρ+R < a := by dsimp only [a]; linarith [le_max_left ρ 0]
  have hab : a < b := by dsimp only [b]; linarith
  obtain ⟨Q,hQ,hN⟩ := hmatch P hε c hc e ha (by linarith) hab
  refine ⟨a,Q,by change ρ+r < a; linarith,hQ,?_⟩
  intro δ₀ k N hδε hk hcenter hscale hfit
  obtain ⟨Θ,F₀,η,hΘ,hmap,hdepth,hzero,K₀,hK₀,hK₀ρ,hfix₀,hfixi₀⟩ :=
    hN N hδε hk hcenter hscale
  have hsource : univ ×ˢ Icc (-R) R ⊆ (neckCentralOpen δ₀ : Set NeckCylinder) := by
    intro q hq
    have hR : R < δ₀⁻¹ := by dsimp only [R,r]; linarith
    exact ⟨mem_univ _,by linarith [hq.2.1],by linarith [hq.2.2]⟩
  have hz (q : Sphere 2) : (q,(0 : ℝ)) ∈ neckCentralOpen δ₀ :=
    ⟨mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩
  let f : neckCentralOpen δ₀ → NeckCylinder := fun q => (Θ q).val
  have hf : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ f :=
    isSmoothEmbedding_fromOpen NeckCylinderModel NeckCylinderModel positiveHornDomain Θ hΘ
  have hdepth' : ∀ q : neckCentralOpen δ₀, q.val ∈ univ ×ˢ Icc (-R) R → ρ < (f q).2 := by
    intro q _
    exact lt_trans (by dsimp only [b]; linarith) (hdepth q)
  obtain ⟨β,σ,hβ,hσ,F,hF,K,hK,hKρ,hfix,hfixi⟩ :=
    exists_reflected_supported_collar_matching_of_embedding (neckCentralOpen δ₀) f hf F₀ η
      hr hrR hρa hsource hz hzero hdepth' K₀ hK₀ hK₀ρ hfix₀
  refine ⟨β,σ,hβ,hσ,F,?_,K,hK,hKρ,hfix,hfixi⟩
  intro q s hs
  obtain ⟨hq,heq⟩ := hF (q,s) hs
  refine ⟨neckCentralOpen_le_buffer δ₀ hq,?_,?_⟩
  · rw [heq]
    exact (Θ ⟨(β q,σ*s),hq⟩).property.2
  · rw [heq]
    exact hmap ⟨(β q,σ*s),hq⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
