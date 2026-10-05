import DifferentialGeometry.Geometry.Fibration.ActualFirstGraph
import DifferentialGeometry.Geometry.Fibration.ActualModelMarkerPlanes

/-!
# TCP05's reference-model table: the comparison data exposed (review 60, draft 59 §1.2)

Blueprint `master207B.tex`, TCP05 (B:5518–5598). `tcp05_row` / `tcp05_row_scale_GAF5` hide the model
`Φ_i` in an existential; the enhanced stage planes (draft 59 §1.2, D59-2) need the WHOLE table: the
model of every reference is the explicit `tcpModelGraph` with the actual support lists
(`tcpListedTags`, `tcpListedEdges`) and TCP05's comparison data `A_c, c_c, A₁, c₁, B_τ, c_τ`. This
module repeats TCP05's per-centre construction and the row (same hypotheses and thresholds) with
those data exposed; smoothness, the own block and the constant scale block of the model are the
general lemmas `contDiff_tcpModelGraph`, `tcpModelGraph_own`, `tcpModelGraph_scale_fderiv_GAFS`.

* `tcp05_centre_table_PLN`: `tcp05_centre_scale_GAF5` (same hypotheses), conclusion
  `∃ A_c c_c A₁ c₁ B_τ c_τ`, global `C²` bounds and (TG) of `tcpModelGraph … (actual lists) …`.
* `tcp05_row_table_PLN`: `tcp05_row_scale_GAF5` (same thresholds and hypotheses), same conclusion.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Analysis.Calculus GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_PLNg : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Centre

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNR_PLNg
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNR_PLNg
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCR_PLNg
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

open Classical in
/-- **TCP05 at one circle reference `i`, with the scale clause** (on `LocalChartPacketsR`; a copy of
`tcp05_centre_KA7` exposing that the model graph `tcpModelGraph …` has a constant scale block):
from TCP03's (TC) clauses
for the listed circle / slim / edge / zero charts (one coisometry each, accuracy `θ/2`) and
TCP04's conclusion at `i`, with FC07's ranges, `θ ≤ e/(100C²)` and `1000CΔΛ < e`, there is a
smooth `Φ_i : ℝ² → H` with own block `(a, 1)`, `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C` and (TG) on
`{|η_i| ≤ 8} ∩ B(i, 200R_i)`: `‖R⁻¹F − Φ_iη_i‖ < e`, `‖R⁻¹dF(w) − DΦ_i dη_i(w)‖ ≤ e|w|`; and
`DΦ_i(a)h` has zero scale block. -/
theorem tcp05_centre_table_PLN
    (P : LocalChartPacketsR X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) {eg θ : ℝ} (heg : 0 < eg) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (hθ : θ ≤ eg / (100 * tcpGraphConst ^ 2))
    (hΔΛ : 1000 * tcpGraphConst * Δ * Λ < eg) {i : X} (hi : i ∈ P.circle.centres)
    (hCrow : ∀ j (hj : j ∈ P.circle.centres),
      (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x ∈ ball i (10 * ρ i),
          ‖(ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj x -
              A (cgpCircleCoord P.toLocalChartFamily i hi x) -
              (ρ j / ρ i) • circleRaw_KA3 P.toLocalChartPacketsD.toLocalChartPackets j i‖ ≤ θ / 2 ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x w -
                A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hSrow : ∀ j (hj : j ∈ P.slim.centres),
      (tsupport (P.slim.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A : ℝ² →L[ℝ] ℝ¹, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x ∈ ball i (10 * ρ i),
          ‖(ρ j / ρ i) • EuclideanSpace.single 0 ((P.slim.centre j hj).coord x) -
              A (cgpCircleCoord P.toLocalChartFamily i hi x) -
              (ρ j / ρ i) • EuclideanSpace.single 0 (slimRaw_KA3 P.toLocalChartFamily j i)‖ ≤
            θ / 2 ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ j / ρ i) • EuclideanSpace.single 0
                  (mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord x w) -
                A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hErow : ∀ j ∈ P.edge.centres,
      (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A : ℝ² →L[ℝ] ℝ¹, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x ∈ ball i (10 * ρ i),
          ‖(ρ j / ρ i) • EuclideanSpace.single 0 (P.edge.coord j x) -
              A (cgpCircleCoord P.toLocalChartFamily i hi x) -
              (ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j i)‖ ≤
            θ / 2 ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ j / ρ i) • EuclideanSpace.single 0 (mvfderiv 𝓘(ℝ, E3) (P.edge.coord j) x w) -
                A (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hZrow : ∀ k (hk : k ∈ P.zero.centres),
      (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
      ∃ A₀ : ℝ² →L[ℝ] ℝ¹,
        A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
        ∀ x ∈ ball i (10 * ρ i),
          ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                ((P.zero.zero k hk).radial x - (P.zero.zero k hk).radial i)) -
              A₀ (cgpCircleCoord P.toLocalChartFamily i hi x)‖ ≤ θ / 2 ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖EuclideanSpace.single 0 ((P.zero.zero k hk).radius / ρ i *
                  mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w) -
                A₀ (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
              θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))
    (hH : ((∀ j ∈ P.edge.centres, ¬ (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty) →
          ∀ j, ∀ x ∈ ball i (10 * ρ i), P.edge.cutoff j x = 0) ∧
        ((∃ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty) →
          (∀ x ∈ ball i (10 * ρ i), P.edge.smoothing x / ρ x < 3 * Δ / 20 ∧
            ∀ j ∈ P.edge.centres, x ∈ ball j (100 * Δ * ρ j) →
              P.edge.cutoff j x = edgeCoordinateProfile (P.edge.coord j x / Δ)) ∨
          ∃ B : ℝ² →L[ℝ] ℝ¹, B.comp (ContinuousLinearMap.adjoint B) = ContinuousLinearMap.id ℝ _ ∧
            ∀ x ∈ ball i (10 * ρ i),
              Δ / 10 ≤ P.edge.smoothing x / ρ x ∧ P.edge.smoothing x / ρ x ≤ 181 * Δ / 20 ∧
              ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => P.edge.smoothing y / ρ y) x ∧
              ‖EuclideanSpace.single 0 (P.edge.smoothing x / ρ x - P.edge.smoothing i / ρ i) -
                  B (cgpCircleCoord P.toLocalChartFamily i hi x -
                    cgpCircleCoord P.toLocalChartFamily i hi i)‖ ≤ θ / 2 ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                ‖EuclideanSpace.single 0
                      (mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x w) -
                    B (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                  θ / 20 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) ∧
                |mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x w| ≤
                  2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))) :
    ∃ (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
      (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
      (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
      (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ),
      (∀ a, ‖fderiv ℝ (tcpModelGraph P.toLocalChartFamily P.zero i
            (tcpListedTags P.toLocalChartFamily P.zero i) (tcpListedEdges P.toLocalChartFamily i)
            Ac cc A1 c1 Bτ cτ) a‖ ≤ tcpGraphConst ∧
        ‖fderiv ℝ (fderiv ℝ (tcpModelGraph P.toLocalChartFamily P.zero i
            (tcpListedTags P.toLocalChartFamily P.zero i) (tcpListedEdges P.toLocalChartFamily i)
            Ac cc A1 c1 Bτ cτ)) a‖ ≤ tcpGraphConst) ∧
      ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
        ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
            (tcpModelGraph P.toLocalChartFamily P.zero i
            (tcpListedTags P.toLocalChartFamily P.zero i) (tcpListedEdges P.toLocalChartFamily i)
            Ac cc A1 c1 Bτ cτ) (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
        ∀ w : TangentSpace 𝓘(ℝ, E3) x,
          ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
              fderiv ℝ (tcpModelGraph P.toLocalChartFamily P.zero i
            (tcpListedTags P.toLocalChartFamily P.zero i) (tcpListedEdges P.toLocalChartFamily i)
            Ac cc A1 c1 Bτ cτ) (cgpCircleCoord P.toLocalChartFamily i hi x)
                (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
            eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  have hri := hρ i
  have hΔ0 : 0 < Δ := by linarith
  have hθ0' := hθ0.le
  have hΔΛs : 100 * Δ * Λ ≤ 1 / 100 := by linarith [mul_nonneg hΔ0.le hΛ]
  have he8 : e ≤ 1 / 8 := by linarith
  have hT20 : (20 : ℝ) ≤ T := by linarith
  have hΛ20 : Λ ≤ 1 / 20 := by
    have hΛΔ : Λ ≤ Δ * Λ := le_mul_of_one_le_left hΛ hΔ
    linarith [mul_nonneg hΔ0.le hΛ]
  obtain ⟨hcnt, hcirc, hslim, hedge, -, hzero⟩ :=
    fc07_input_packet P.toLocalChartPacketsD.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT i
  have hγ : 0 ≤ γ := circle_quality_nonneg_KA4 P.toLocalChartPacketsD.toLocalChartPackets hi
  obtain ⟨-, -, hS1, hE1, -, -, -⟩ :=
    tcp01_row P.toLocalChartPacketsD.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT hγ hi
  choose! Acf hAcf using hCrow
  choose! Asf hAsf using hSrow
  choose! Aef hAef using hErow
  choose! Azf hAzf using hZrow
  obtain ⟨τf, Bτ, cτ, hBτ, hcut, hτm, hτx⟩ := tcp05_height_data_KA7
    P.toLocalChartPacketsD.toLocalChartPackets hΔ hi hθ0'
    (fun j hj hm => (hedge j hj hm).2.2.1.trans (hedge j hj hm).2.2.2.1) hH
  obtain ⟨hcount, hcountE⟩ := tcpListed_card_KA7 P.toLocalChartFamily P.zero i hcnt
  set S := tcpListedTags P.toLocalChartFamily P.zero i with hSdef
  set Se := tcpListedEdges P.toLocalChartFamily i with hSedef
  set Ac := tcpAcOf P.toLocalChartFamily P.zero Acf with hAcdef
  set cc := tcpCcOf P.toLocalChartPacketsD.toLocalChartPackets i with hccdef
  set A1 := tcpA1Of P.toLocalChartFamily P.zero i Asf Aef Azf with hA1def
  set c1 := tcpC1Of P.toLocalChartFamily P.zero i with hc1def
  have hown : ∀ j : P.circle.finite_centres.toFinset, j.1 = i →
      (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ S :=
    fun j h => (mem_tcpListedTags_KA7 (i := i)).mpr (Or.inl h)
  have hSe : ∀ j : P.toLocalChartFamily.edge.finite_centres.toFinset,
      (.inr (.inr (.inl j)) : CGPTag P.toLocalChartFamily P.zero) ∉ S :=
    fun j h => (mem_tcpListedTags_KA7 (i := i)).mp h
  have hClist : ∀ j : P.circle.finite_centres.toFinset, j.1 ≠ i →
      (.inl j : CGPTag P.toLocalChartFamily P.zero) ∈ S →
      (tsupport (P.circle.cutoff j.1) ∩ ball i (10 * ρ i)).Nonempty := by
    intro j hji hjS
    rcases (mem_tcpListedTags_KA7 (i := i)).mp hjS with h | h
    · exact (hji h).elim
    · exact h
  have hzs : ∀ k : P.zero.finite_centres.toFinset,
      (.inr (.inr (.inr (.inl k))) : CGPTag P.toLocalChartFamily P.zero) ∈ S →
      1 ≤ (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / ρ i := by
    intro k hkS
    have hm := (mem_tcpListedTags_KA7 (i := i)).mp hkS
    have hk := (Set.Finite.mem_toFinset _).mp k.2
    have hsh := ((hzero k.1 hk hm).1 i (mem_ball_self (by positivity))).2
    have hib : i ∈ ball k.1 (P.zero.zero k.1 hk).radius := by
      rw [mem_ball, dist_comm]
      have := (P.zero.zero k.1 hk).radius_pos
      linarith
    have h := LocalChartPacketsR.zero_ratio_of_meets P hT20 hΛ20 hk
      ⟨i, hib, mem_ball_self (by positivity)⟩
    have : (1 : ℝ) ≤ T / 20 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  refine ⟨Ac, cc, A1, c1, Bτ, cτ, fun a => ?_, fun x hxi h8 => ?_⟩
  · refine tcp05_model_bounds P.toLocalChartFamily P.zero i S Se Ac cc A1 c1 Bτ cτ hΔ hown
      (fun j hji hjS => ?_) (fun j hjS => ?_) (fun k hkS => ⟨?_, hzs k hkS⟩) (fun j hj => ?_)
      (hBτ.trans one_le_two) hcount hcountE a
    · have hm := hClist j hji hjS
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      exact ⟨DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ (hAcf j.1 hj hm).1,
        (hcirc j.1 hj hm).1⟩
    · have hm := (mem_tcpListedTags_KA7 (i := i)).mp hjS
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      exact ⟨norm_proj_comp_le_KA7 _
        (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ (hAsf j.1 hj hm).1),
        (hS1 j.1 hj hm).1.1.le⟩
    · have hm := (mem_tcpListedTags_KA7 (i := i)).mp hkS
      have hk := (Set.Finite.mem_toFinset _).mp k.2
      exact norm_proj_comp_le_KA7 _
        (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ (hAzf k.1 hk hm).1)
    · have hm := (mem_tcpListedEdges_KA7 (i := i)).mp hj
      have hjc := (Set.Finite.mem_toFinset _).mp j.2
      have hr := (hedge j.1 hjc hm).1
      exact ⟨norm_edge_row_le_KA7 hr.1 _
        (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ (hAef j.1 hjc hm).1), hr⟩
  · have hx : x ∈ ball i (10 * ρ i) :=
      mem_ball.mpr (LocalChartPacketsR.dist_lt_of_norm_coord_le P hi (mem_ball.mp hxi) h8)
    have hF : MDifferentiableAt 𝓘(ℝ, E3)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (cgpGlobalMap P.toLocalChartFamily P.zero) x :=
      (cgp01_rowE P.toLocalChartPacketsD.toLocalChartPackets.toLocalChartFamilyE P.zero hΛ hΔ0 hμ hτ
        hΔΛs he8).mdifferentiableAt (by simp)
    have hpt := tcp05_point_KA7 P.toLocalChartPacketsD.toLocalChartPackets hi S Se Ac cc A1 c1 Bτ cτ
      τf hθ0' hθ1 hΔ hΛ hF hx hxi h8 hown hSe (fun j hji hjS => ?_) (fun j hjS => ?_)
      (fun k hkS => ?_) (fun k => ?_) ?_ hcut
      (fun y hy k hk => image_eq_zero_of_notMem_tsupport
        (fun hyt => hk ((mem_tcpListedEdges_KA7 (i := i)).mpr ⟨y, hyt, hy⟩)))
      hτm hcountE
      (fun j hji hjS hxt => hjS ((mem_tcpListedTags_KA7 (i := i)).mpr (Or.inr ⟨x, hxt, hx⟩)))
      (fun j hjS hxt => hjS ((mem_tcpListedTags_KA7 (i := i)).mpr ⟨x, hxt, hx⟩))
      (fun k hkS hxt => hkS ((mem_tcpListedTags_KA7 (i := i)).mpr ⟨x, hxt, hx⟩))
    · have hcardA := tcpModelActive_card_le_KA6 P.toLocalChartFamily P.zero S Se hcount
      have hlt := tcp05_budget_lt_KA7 heg hθ0' hθ hΔ hΛ hΔΛ (Nat.cast_nonneg _) hcardA
      refine ⟨hpt.1.trans_lt hlt, fun w => (hpt.2 w).trans ?_⟩
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hlt.le (Real.sqrt_nonneg _)
    · -- listed circle blocks
      have hm := hClist j hji hjS
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      obtain ⟨hco, hTC⟩ := hAcf j.1 hj hm
      obtain ⟨hratio, -, hsub1, hsub2, -⟩ := hcirc j.1 hj hm
      exact ⟨hsub2 (hsub1 hx), hratio,
        DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ hco, (hTC x hx).1,
        (hTC x hx).2⟩
    · -- listed slim blocks
      have hm := (mem_tcpListedTags_KA7 (i := i)).mp hjS
      have hj := (Set.Finite.mem_toFinset _).mp j.2
      obtain ⟨hco, hTC⟩ := hAsf j.1 hj hm
      obtain ⟨-, -, -, hsub, hsub', -⟩ := hslim j.1 hj hm
      obtain ⟨hratio', hsm⟩ := hS1 j.1 hj hm
      exact ⟨hsub' (hsub hx), hratio'.1.le,
        (hsm.contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp),
        norm_proj_comp_le_KA7 _
          (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ hco),
        slim_conv_KA7 _ _ (hTC x hx).1, fun w => deriv_conv_KA7 _ _ ((hTC x hx).2 w)⟩
    · -- the zero block
      have hm := (mem_tcpListedTags_KA7 (i := i)).mp hkS
      have hk := (Set.Finite.mem_toFinset _).mp k.2
      obtain ⟨hco, hTC⟩ := hAzf k.1 hk hm
      obtain ⟨-, O, hO, hDO, hsmO⟩ := hzero k.1 hk hm
      refine ⟨hzs k hkS, (hsmO.contMDiffAt (hO.mem_nhds (hDO hx))).mdifferentiableAt (by simp),
        norm_proj_comp_le_KA7 _
          (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ hco),
        zero_conv_KA7 _ _ (hTC x hx).1, fun w => ?_⟩
      have h := (hTC x hx).2 w
      rw [norm_single_sub_eq_KA5] at h
      exact h
    · -- the listed edge coordinates
      have hm := (mem_tcpListedEdges_KA7 (i := i)).mp k.2
      have hjc := (Set.Finite.mem_toFinset _).mp k.1.2
      obtain ⟨hco, hTC⟩ := hAef k.1.1 hjc hm
      have hr := (hedge k.1.1 hjc hm).1
      obtain ⟨-, hsm⟩ := hE1 k.1.1 hjc hm
      refine ⟨hr, norm_edge_row_le_KA7 hr.1 _
          (DifferentialGeometry.Geometry.Fibration.norm_coisometry_le_one _ hco),
        hsm.contMDiffAt (isOpen_ball.mem_nhds hx),
        (edge_conv_KA7 hr.1 _ _ (hTC x hx).1).trans (by linarith), fun w => ?_⟩
      refine (edge_deriv_conv_KA7 hr.1 _ _ ((hTC x hx).2 w)).trans (le_of_eq ?_)
      ring
    · -- the height input
      obtain ⟨h1, h2, h3⟩ := hτx x hx
      refine ⟨h1, hBτ.trans one_le_two, h2.trans (by linarith), fun w => (h3 w).trans ?_⟩
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

end Centre

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_PLNr {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNr {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNr {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP05 with the scale clause** (`thm:fibration-actual-first-graph`, B:5518; `tcp05_row` with
the additional conclusion that `DΦ_i` has zero scale block) on `LocalChartPacketsC14`: for an early
`0 < e < 1/100` (and the exclusion quality `ν`, `3ν ≤ β₃ < 1`) there are early `σ`, `η₂`, `γ₀`,
`η_c` and `θ < 1` (all before `Δ`) and for every `Δ ≥ 1200` a later `η₁`, such that with FC07's
ranges, TCP03's and TCP04's quality bounds at `θ` and `1000CΔΛ < e`, at every circle centre `i`
there is a smooth `Φ_i : ℝ² → H` with own block `(a, 1)`, `‖DΦ_i‖, ‖D²Φ_i‖ ≤ C` (`C =
tcpGraphConst`, fixed before `Δ`) and (TG) on `{|η_i| ≤ 8} ∩ B(i, 200R_i)`:
`‖R_i⁻¹F − Φ_iη_i‖ < e` and `‖R_i⁻¹dF(w) − DΦ_i dη_i(w)‖ ≤ e|w|` (`|w|` of `R_i⁻²g`). -/
theorem tcp05_row_table_PLN {eg ν : ℝ} (heg : 0 < eg) (heg1 : eg < 1 / 100) (hν : 0 < ν)
    (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧
    θ < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
        e T V vs ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      ∀ i (hi : i ∈ P.circle.centres),
        ∃ (Ac : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ²)
          (cc : CGPTag P.toLocalChartFamily P.zero → ℝ²)
          (A1 : CGPTag P.toLocalChartFamily P.zero → ℝ² →L[ℝ] ℝ)
          (c1 : CGPTag P.toLocalChartFamily P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ),
          (∀ a, ‖fderiv ℝ (tcpModelGraph P.toLocalChartFamily P.zero i
                (tcpListedTags P.toLocalChartFamily P.zero i) (tcpListedEdges P.toLocalChartFamily i)
                Ac cc A1 c1 Bτ cτ) a‖ ≤ tcpGraphConst ∧
            ‖fderiv ℝ (fderiv ℝ (tcpModelGraph P.toLocalChartFamily P.zero i
                (tcpListedTags P.toLocalChartFamily P.zero i) (tcpListedEdges P.toLocalChartFamily i)
                Ac cc A1 c1 Bτ cτ)) a‖ ≤ tcpGraphConst) ∧
          ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord P.toLocalChartFamily i hi x‖ ≤ 8 →
            ‖(ρ i)⁻¹ • cgpGlobalMap P.toLocalChartFamily P.zero x -
                (tcpModelGraph P.toLocalChartFamily P.zero i
                (tcpListedTags P.toLocalChartFamily P.zero i) (tcpListedEdges P.toLocalChartFamily i)
                Ac cc A1 c1 Bτ cτ) (cgpCircleCoord P.toLocalChartFamily i hi x)‖ < eg ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) x w -
                  fderiv ℝ (tcpModelGraph P.toLocalChartFamily P.zero i
                (tcpListedTags P.toLocalChartFamily P.zero i) (tcpListedEdges P.toLocalChartFamily i)
                Ac cc A1 c1 Bτ cτ) (cgpCircleCoord P.toLocalChartFamily i hi x)
                    (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x w)‖ ≤
                eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  obtain ⟨hθ0, hθ1⟩ := tcp05_theta_KA7 heg heg1
  set θ := eg / (100 * tcpGraphConst ^ 2) with hθdef
  have hθ21 : θ ^ 2 / 1000 ≤ 1 := by
    have h1 : θ ^ 2 ≤ 1 := by nlinarith
    linarith
  obtain ⟨σ1, hσ1, hσ11, η21, hη21, γ01, hγ01, hcirc⟩ := tcp03_circle_row hθ0 hθ1 hν hν1
  obtain ⟨σ2, hσ2, -, γ02, hγ02, hslim⟩ := tcp03_slim_row hθ0 hθ1 hν hν1
  obtain ⟨σ3, hσ3, -, γ03, hγ03, hedge⟩ := tcp03_edge_row hθ0 hθ1 hν hν1
  obtain ⟨σ4, hσ4, -, η24, hη24, γ04, hγ04, η14, hη14, hzero⟩ := tcp03_zero_row hθ0 hθ1 hν hν1
  obtain ⟨σ5, hσ5, -, η25, hη25, γ05, hγ05, ηc, hηc, hheight⟩ := tcp04_row hθ0 hθ1 hν hν1
  set σ := min σ1 (min σ2 (min σ3 (min σ4 σ5))) with hσdef
  have hσ0 : 0 < σ := lt_min hσ1 (lt_min hσ2 (lt_min hσ3 (lt_min hσ4 hσ5)))
  have hσle1 : σ ≤ σ1 := min_le_left _ _
  have hσle2 : σ ≤ σ2 := (min_le_right _ _).trans (min_le_left _ _)
  have hσle3 : σ ≤ σ3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hσle4 : σ ≤ σ4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hσle5 : σ ≤ σ5 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  set η₂ := min η21 (min η24 η25) with hη₂def
  set γ₀ := min γ01 (min γ02 (min γ03 (min γ04 γ05))) with hγ₀def
  refine ⟨σ, hσ0, hσle1.trans hσ11, η₂, γ₀, ηc, θ, lt_min hη21 (lt_min hη24 hη25),
    lt_min hγ01 (lt_min hγ02 (lt_min hγ03 (lt_min hγ04 hγ05))), hηc, hθ0, hθ1,
    fun Δ hΔ => ?_⟩
  obtain ⟨η12, hη12, hslimΔ⟩ := hslim Δ (by linarith)
  obtain ⟨η13, hη13, hedgeΔ⟩ := hedge Δ (by linarith)
  refine ⟨min η12 (min η13 η14), lt_min hη12 (lt_min hη13 hη14), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hμ hτ hLΛ hLmax he hT hε hε1 hσc0 hσcθ hμΔ hν3 hβ3 h3β2 hβ2 hγ hγc hγcγ hβc hb hβ1 hσs
    hσsθ hvs hζ hζθ hεr hΛz hσL hΔΛ i hi
  have hΔ1 : (1 : ℝ) ≤ Δ := le_trans (by norm_num) hΔ
  have hinv : ∀ σ' : ℝ, σ ≤ σ' → σ'⁻¹ ≤ Lmax := fun σ' h => (inv_anti₀ hσ0 h).trans hσL
  have hγ' : ∀ γ' : ℝ, γ₀ ≤ γ' → γ ≤ γ' := fun γ' h => hγ.trans h
  have hCrow := hcirc P.toLocalChartPackets hΛ hΔ1 hμ hτ hLΛ hLmax he hT hν3 hβ3
    (h3β2.trans hσle1) (hβ2.trans (min_le_left _ _))
    (hγ' _ (min_le_left _ _)) (hinv _ hσle1) i hi
  have hSrow := hslimΔ P.toLocalChartPacketsRVZ.toLocalChartPacketsRV hΛ hμ hτ hLΛ hLmax he hT hν3
    hβ3 (h3β2.trans hσle2) (hγ' _ ((min_le_right _ _).trans (min_le_left _ _)))
    (hβ1.trans (min_le_left _ _)) hσs hσsθ hvs (hinv _ hσle2) i hi
  have hErow := hedgeΔ P.toLocalChartPackets hΛ hμ hτ hLΛ hLmax he hT hν3 hβ3 (h3β2.trans hσle3)
    (hγ' _ ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    (hb.trans ((min_le_right _ _).trans (min_le_left _ _))) hσcθ hμΔ (hinv _ hσle3) i hi
  have hZrow := hzero P.toLocalChartPacketsRVZ.toLocalChartPacketsZ hΛ hΔ1 hLΛ he hT hν3 hβ3
    (h3β2.trans hσle4) (hβ2.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hγ' _ ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
    (hβ1.trans ((min_le_right _ _).trans (min_le_right _ _))) hζ hζθ hεr hΛz (hinv _ hσle4) i hi
  have hH := hheight P.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT hε hε1 hσc0
    (hσcθ.trans hθ21) hν3 hβ3 (h3β2.trans hσle5)
    (hβ2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (hγ' _ ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))))
    hγc (hγcγ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))) hβc (hinv _ hσle5) i hi
  exact tcp05_centre_table_PLN P.toLocalChartPacketsR hΛ hΔ1
    hμ hτ hLΛ hLmax he hT heg hθ0 hθ1.le le_rfl hΔΛ hi
    (fun j hj hm => by
      obtain ⟨A, hA, -, hTC⟩ := hCrow j hj hm
      exact ⟨A, hA, hTC⟩)
    (fun j hj hm => by
      obtain ⟨A, hA, -, hTC⟩ := hSrow j hj hm
      exact ⟨A, hA, hTC⟩)
    (fun j hj hm => by
      obtain ⟨A, hA, -, hTC⟩ := hErow j hj hm
      exact ⟨A, hA, hTC⟩)
    (fun k hk hm => by
      obtain ⟨A, hA, -, hTC⟩ := hZrow k hk hm
      exact ⟨A, hA, hTC⟩)
    hH

end DifferentialGeometry.Geometry.Collapse
