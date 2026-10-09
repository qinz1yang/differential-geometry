import DifferentialGeometry.Geometry.Metric.LargeCloudBufferedGraphProximity
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutput

/-!
# CFS12 and CFS13: the large spectral section and the global buffered graphs (row forms)

Blueprint `master207B.tex`, CFS12 (`lem:fibration-cloud-large-spectral`, B:2513–2569) and CFS13
(`prop:fibration-cloud-global-buffered-graphs`, B:2571–2626), with the standing hypotheses of
B:2425–2449: a bounded cloud `S ⊆ S̃` with `k`-planes, radius bounded above and away from zero, (MCb)
at the buffer `128b` (here with any `B ≥ 1`; the blueprint's `B = 5/3`), and the (CS) tests at
quality `δ`. "Sufficiently small `δ`" is a threshold `δ₀(k, b, B) > 0` chosen before the data (the
kernels' interior condition `δ((80B + 31)b + 2) < 1` is folded into it).

* `cfs12_row_CFSA` (CFS12): on CFS11's selection, the weights `w_i` (cutoffs at `40br_i`) with
  their jets on both reference balls `V_x = B(x, 8br_x)` (`x ∈ S`) and `V_i = B(x_i, 30br_i)`, the
  spectral projector `Q` of `O = Σ w_i P_i` smooth of rank `dim H − k` on `Ω_b`, the single
  section `η = Q(· − μ)` smooth on `Ω_b`, and (LS) for `Q` and `η` on both kinds of reference balls
  (constants `C_m, E_m` independent of `dim H` and of the data).
* `cfs13_row_CFSA` (CFS13): `W = {z ∈ U_b | η z = 0}` properly embedded in `U_b`, a smooth embedded
  `k`-manifold; for every `x ∈ S` a smooth graph `g_x` over `B_{L_x}(0, 4br_x)` in `W` with
  `|g_x| ≤ r_x/4`, the normal uniqueness on `|n| ≤ r_x`, (GG) `‖D^q g_x‖ ≤ F_m δ r_x^{1−q}` and (GI)
  `W ∩ B(x, 3br_x) = G_x ∩ B(x, 3br_x)` (also `W ⊆ N_r(S̃)`).
* `Cfs15StageOutput.cfs13_clauses_CFSA`: CFS13's conclusions at `b = ε⁻¹` read off a native output,
  (GG) in the common-small-bound form `‖D^q g_x‖ ≤ (ε/3) r_x^{1−q}` (`q ≤ K + 1`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold

namespace GC.MetricGeometry

universe u

/-- **CFS12** (`lem:fibration-cloud-large-spectral`): for `k`, `b ≥ 1`, `B ≥ 1` there are constants
`C_m, E_m` and a threshold `δ₀ > 0` such that every cloud with the standing hypotheses and (CS) at
quality `0 < δ ≤ δ₀` has CFS11's selection with the weights, the smooth rank-`(dim H − k)` spectral
projector `Q`, the smooth section `η` on `Ω_b`, and (LS) on every reference ball. -/
theorem cfs12_row_CFSA
    (k : ℕ) (b B : ℝ) (hb : 1 ≤ b) (hB : 1 ≤ B) :
    ∃ C E : ℕ → ℝ≥0, ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ →
        (∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * b * max (r y) (r x) →
          r x / B ≤ r y ∧ r y ≤ B * r x) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (r i)) ∧
          (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
          ((⋃ x ∈ S, ball x (8 * b * r x)) ⊆ ⋃ i ∈ I, ball i (20 * b * r i)) ∧
          let w : H → H → ℝ := fun i y => ballCutoff i (40 * b * r i) (2 * (40 * b * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * b * r a) (2 * (40 * b * r a)) y)
          let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          (∀ m, ∀ x ∈ S, ∀ j ≤ m, ∀ z ∈ ball x (8 * b * r x),
            (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w i) z‖) ≤ (C m : ℝ) / (r x) ^ j) ∧
          (∀ m, ∀ i ∈ I, ∀ j ≤ m, ∀ z ∈ ball i (30 * b * r i),
            (∑ a ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w a) z‖) ≤ (C m : ℝ) / (r i) ^ j) ∧
          (∀ x ∈ S, ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball x (8 * b * r x)) ∧
              (∀ z ∈ ball x (8 * b * r x), Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
                ‖(Q z).starProjection - (P x)ᗮ.starProjection‖ ≤ 24 * (B + 1) * δ) ∧
              ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball x (8 * b * r x),
                ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection - (P x)ᗮ.starProjection) z‖ ≤
                  max 4 ((resolventDerivativeBound 4 (C m) j : ℝ) / 2) *
                    (6 * (B + 1)) * δ / (r x) ^ j) ∧
          (∀ i ∈ I, ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball i (30 * b * r i)) ∧
              (∀ z ∈ ball i (30 * b * r i), Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
                ‖(Q z).starProjection - (P i)ᗮ.starProjection‖ ≤ 24 * (B + 1) * δ) ∧
              ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball i (30 * b * r i),
                ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection - (P i)ᗮ.starProjection) z‖ ≤
                  max 4 ((resolventDerivativeBound 4 (C m) j : ℝ) / 2) *
                    (6 * (B + 1)) * δ / (r i) ^ j) ∧
          let η : H → H := fun y => (Q y).starProjection
            (y-∑ i ∈ hI.toFinset, w i y • i)
          let Ω : Set H := ⋃ i ∈ I, ball i (30*b*r i)
          ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) Ω ∧
          (∀ z ∈ Ω, Module.finrank ℝ (Q z)=Module.finrank ℝ H-k) ∧
          ContDiffOn ℝ ∞ η Ω ∧
          (∀ m, ∀ x ∈ S, ∀ j ≤ m, ∀ z ∈ ball x (8*b*r x),
            ‖iteratedFDeriv ℝ j (fun y => η y-(P x)ᗮ.starProjection (y-x)) z‖ ≤
              (E m : ℝ)*δ*r x*((r x)⁻¹)^j) ∧
          (∀ m, ∀ i ∈ I, ∀ j ≤ m, ∀ z ∈ ball i (30*b*r i),
            ‖iteratedFDeriv ℝ j (fun y => η y-(P i)ᗮ.starProjection (y-i)) z‖ ≤
              (E m : ℝ)*δ*r i*((r i)⁻¹)^j) := by
  obtain ⟨C, E, hker⟩ := exists_uniform_large_cloud_displacement_jets.{u} k b B hb hB
  have hA : 0 < (80 * B + 31) * b + 2 := by
    have : 0 < b := zero_lt_one.trans_le hb
    have : 0 < B := zero_lt_one.trans_le hB
    positivity
  refine ⟨C, E, 1 / (2 * ((80 * B + 31) * b + 2)), by positivity, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδs hscale hcloud
  have hint : δ * ((80 * B + 31) * b + 2) < 1 := by
    have h1 : δ * (2 * ((80 * B + 31) * b + 2)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hδs
    nlinarith
  exact hker H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hint hscale hcloud

/-- **CFS13** (`prop:fibration-cloud-global-buffered-graphs`): for `k`, `b ≥ 1`, `B ≥ 1` there are
`F_m ≥ 0` and `δ₀ > 0` such that every cloud with the standing hypotheses ((MCb) on `S̃`) and (CS)
at quality `0 < δ ≤ δ₀` has: `W = {z ∈ U_b | η z = 0}` properly embedded in `U_b` and a smooth
embedded `k`-manifold, and for every `x ∈ S` one graph `G_x ⊆ W` over `B_{L_x}(0, 4br_x)` with (GG)
and (GI) (plus `W ⊆ N_r(S̃)`). -/
theorem cfs13_row_CFSA
    (k : ℕ) (b B : ℝ) (hb : 1 ≤ b) (hB : 1 ≤ B) :
    ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ →
        (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * b * max (r y) (r x) →
          r x / B ≤ r y ∧ r y ≤ B * r x) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (r i)) ∧
          (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
          ((⋃ x ∈ S, ball x (8 * b * r x)) ⊆ ⋃ i ∈ I, ball i (20 * b * r i)) ∧
          let w : H → H → ℝ := fun i y => ballCutoff i (40 * b * r i) (2 * (40 * b * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * b * r a) (2 * (40 * b * r a)) y)
          let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          let η : H → H := fun y => (Q y).starProjection
            (y - ∑ i ∈ hI.toFinset, w i y • i)
          let U : Set H := ⋃ i ∈ I, ball i (20 * b * r i)
          let Z : Set H := {z | z ∈ U ∧ η z = 0}
          (IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : U)) ∧
            ∃ cs : ChartedSpace (Fin k → ℝ) Z,
              let _ := cs
              IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
              _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
                (Subtype.val : Z → H)) ∧
          (Z ⊆ ⋃ q ∈ T, ball q (r q)) ∧
          ∃ g : ∀ x : S, P x → (P x)ᗮ, ∀ x : S,
            ContDiffOn ℝ ∞ (g x) (ball 0 (4 * b * r x)) ∧
            (∀ t ∈ ball (0 : P x) (4 * b * r x), ‖g x t‖ ≤ r x / 4 ∧
              (x : H) + orthogonalCoordinateSum (P x) (t, g x t) ∈ Z) ∧
            (∀ t ∈ ball (0 : P x) (4 * b * r x),
              ∀ n ∈ closedBall (0 : (P x)ᗮ) (r x),
              η ((x : H) + orthogonalCoordinateSum (P x) (t, n)) = 0 ↔ n = g x t) ∧
            (∀ m t, t ∈ ball (0 : P x) (4 * b * r x) → ∀ j, j ≤ m →
              ‖iteratedFDeriv ℝ j (g x) t‖ ≤ F m * δ * r x * ((r x)⁻¹) ^ j) ∧
            Z ∩ ball (x : H) (3 * b * r x) =
              {z : H | ∃ t ∈ ball (0 : P x) (4 * b * r x),
                z = (x : H) + orthogonalCoordinateSum (P x) (t, g x t)} ∩
                  ball (x : H) (3 * b * r x) := by
  obtain ⟨F, hF, δ₀, hδ₀, hker⟩ :=
    exists_uniform_large_cloud_buffered_graph_manifold_with_proximity.{u} k b B 1 hb hB one_pos
  have hA : 0 < (80 * B + 31) * b + 2 := by
    have : 0 < b := zero_lt_one.trans_le hb
    have : 0 < B := zero_lt_one.trans_le hB
    positivity
  refine ⟨F, hF, min δ₀ (1 / (2 * ((80 * B + 31) * b + 2))), lt_min hδ₀ (by positivity), ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδs hscale hcloud
  have hint : δ * ((80 * B + 31) * b + 2) < 1 := by
    have h1 : δ * (2 * ((80 * B + 31) * b + 2)) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (hδs.trans (min_le_right _ _))
    nlinarith
  have h := hker H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ (hδs.trans (min_le_left _ _))
    hint hscale hcloud
  simpa only [one_mul] using h

/-- **CFS13 on a native output** (\`b = ε⁻¹\`): the zero set \`W = O.Z\` lies in the tube \`U_b\`, is properly
embedded in \`U_b\` and a smooth embedded \`k\`-manifold; for every \`x ∈ S\` the graph \`g_x\` over
\`B_{L_x}(0, 4br_x)\` is smooth, \`|g_x| ≤ r_x/4\`, its points lie in \`W\`, the normal coordinate is unique
on \`|n| ≤ r_x\`, (GI) \`W ∩ B(x, 3br_x) = G_x ∩ B(x, 3br_x)\`, and (GG) in the common-small-bound form
\`‖D^q g_x‖ ≤ (ε/3) r_x^{1−q}\` for \`q ≤ K + 1\`. -/
theorem Cfs15StageOutput.cfs13_clauses_CFSA {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] {k K : ℕ} {ε cw : ℝ} {S T : Set H}
    {r : H → ℝ} {P : H → Submodule ℝ H} (O : Cfs15StageOutput k K ε cw S T r P) :
    O.Z ⊆ cfs15Tube_C15 ε r O.I ∧
      IsProperMap (fun z : O.Z => (⟨z.1, z.2.1⟩ : cfs15Tube_C15 ε r O.I)) ∧
      (let _ := O.cs
       IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ O.Z ∧
        _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞ (Subtype.val : O.Z → H)) ∧
      ∀ x : S,
        ContDiffOn ℝ ∞ (O.g x) (ball 0 (4 * ε⁻¹ * r x)) ∧
        (∀ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x), ‖O.g x t‖ ≤ r x / 4 ∧
          (x : H) + orthogonalCoordinateSum (P x) (t, O.g x t) ∈ O.Z) ∧
        (∀ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x), ∀ n ∈ closedBall (0 : (P x)ᗮ) (r x),
          cfs15Section_C15 ε r P O.hI ((x : H) + orthogonalCoordinateSum (P x) (t, n)) = 0 ↔
            n = O.g x t) ∧
        O.Z ∩ ball (x : H) (3 * ε⁻¹ * r x) =
          {z : H | ∃ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x),
            z = (x : H) + orthogonalCoordinateSum (P x) (t, O.g x t)} ∩
            ball (x : H) (3 * ε⁻¹ * r x) ∧
        ∀ j ≤ K + 1, ∀ t ∈ ball (0 : P x) (4 * ε⁻¹ * r x),
          ‖iteratedFDeriv ℝ j (O.g x) t‖ ≤ (ε / 3) * r x * ((r x)⁻¹) ^ j :=
  ⟨fun _ hz => hz.1, O.proper, ⟨O.isManifold, O.embedding⟩, fun x =>
    ⟨O.graph_smooth x, O.graph_mem x, fun _ ht _ hn => Cfs15StageOutput.graph_unique_iff ht hn,
      O.graph_eq x, fun j hj t ht => O.graph_jets x t ht j hj⟩⟩

end GC.MetricGeometry
