import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProductChartCircle

/-!
# G17 kernels: a compiled consumer on the model circle bundle (S-BAUG-D2)

`circleBundle_record_chart_BAUGD`: the circle-stage kernel
`smoothProductChartAt_circle_of_record_BAUGD` applied to the model situation `ℝ² × S¹ → ℝ²`
(`ι = id`, `f = fst`, `κ = id`, `σ₀ = id`, the big base `Wb = ball 0 1`, the open marked set
`Mk = univ`, `O' = univ`, `X = fst⁻¹ ball 0 1`): over every point of the unit disk the whole fibre
has a smooth product chart `ℝ² × S¹`. This shows the hypotheses of the kernel (record, openness,
properness over compacta, connected whole fibre, submersion) are satisfiable and mutually
consistent; the actual stage hypotheses are the ones of the boundary chain.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- **The model circle bundle through the circle-stage kernel**. -/
theorem circleBundle_record_chart_BAUGD {y : ℝ²}
    (hy : y ∈ ball (0 : ℝ²) 1) :
    SmoothProductChartAt_BIFc ((𝓡 2).prod (𝓡 1)) (𝓡 1) (F := Circle) 2
      (Prod.fst : ℝ² × Circle → ℝ²)
      (Prod.fst ⁻¹' ball (0 : ℝ²) 1) (ball (0 : ℝ²) 1)
      y := by
  let X : Set (ℝ² × Circle) :=
    Prod.fst ⁻¹' ball (0 : ℝ²) 1
  have hXopen : IsOpen X := isOpen_ball.preimage continuous_fst
  have hdim : Module.finrank ℝ (ℝ² × EuclideanSpace ℝ (Fin 1)) = 2 + 1 := by
    simp [Module.finrank_prod]
  have himg : (Prod.fst : ℝ² × Circle → ℝ²) '' X =
      ball (0 : ℝ²) 1 :=
    Prod.fst_surjective.image_preimage _
  have hreg : ∀ x : ℝ² × Circle, id x ∈ X → True →
      Surjective (mfderiv ((𝓡 2).prod (𝓡 1)) (𝓡 2)
        (fun x : ℝ² × Circle =>
          (ContinuousLinearMap.id ℝ (ℝ²))
            ((Prod.fst : ℝ² × Circle → ℝ²) (id x))) x) := by
    intro x _ _
    change Surjective (mfderiv ((𝓡 2).prod (𝓡 1)) (𝓡 2) Prod.fst x)
    rw [mfderiv_fst]
    exact Prod.fst_surjective
  have hprop : ∀ Kc ⊆ ball (0 : ℝ²) 1, IsCompact Kc →
      IsCompact (X ∩ (Prod.fst : ℝ² × Circle → ℝ²) ⁻¹' Kc) := by
    intro Kc hK hKc
    have : X ∩ (Prod.fst : ℝ² × Circle → ℝ²) ⁻¹' Kc =
        Kc ×ˢ (univ : Set Circle) := by
      ext p
      constructor
      · rintro ⟨-, hp⟩
        exact ⟨hp, mem_univ _⟩
      · rintro ⟨hp, -⟩
        exact ⟨hK hp, hp⟩
    rw [this]
    exact hKc.prod isCompact_univ
  have hconn : IsConnected {x : ℝ² × Circle |
      id x ∈ X ∧ (Prod.fst : ℝ² × Circle → ℝ²) (id x) = y} := by
    have : {x : ℝ² × Circle |
        id x ∈ X ∧ (Prod.fst : ℝ² × Circle → ℝ²)
          (id x) = y} = ({y} : Set (ℝ²)) ×ˢ (univ : Set Circle) := by
      ext p
      constructor
      · rintro ⟨-, hp⟩
        exact ⟨hp, mem_univ _⟩
      · rintro ⟨hp, -⟩
        exact ⟨show p.1 ∈ ball (0 : ℝ²) 1 by rw [hp]; exact hy, hp⟩
    rw [this]
    exact isConnected_singleton.prod isConnected_univ
  exact smoothProductChartAt_circle_of_record_BAUGD (I := (𝓡 2).prod (𝓡 1))
    (IM := (𝓡 2).prod (𝓡 1)) (k := 2) (by norm_num) hdim id IsSmoothEmbedding.id
    (fun _ => BoundarylessManifold.isInteriorPoint) Prod.fst X (ball 0 1)
    (ContinuousLinearMap.id ℝ (ℝ²)) id (ball 0 1) univ univ univ (r := 1)
    (by rw [inter_univ]) isOpen_univ isOpen_univ isOpen_univ contDiffOn_id
    (fun b hb => ⟨⟨hb, mem_univ _⟩, rfl⟩) (fun w hw => ⟨hw.1, rfl⟩) (fun p _ => ⟨p, rfl⟩)
    himg hXopen continuous_fst (contMDiff_fst) (fun x hx _ _ => hreg x hx trivial) hprop hy
    (mem_univ _) (mem_univ _) hconn

end DifferentialGeometry.Geometry.Collapse
