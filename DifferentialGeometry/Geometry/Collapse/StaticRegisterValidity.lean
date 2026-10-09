import DifferentialGeometry.Geometry.Collapse.LocalExport.ClosedMemberModel
import DifferentialGeometry.Geometry.Collapse.StaticRegisterFamilyAdapter
import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.KL618Tail
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.RankExclusion
import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoice

/-!
# The closed threshold validity (lane FC39-VAL; external review 49, B.1, T49-4)

Design `build-logs/resume/design-FC39-VAL.md` §1, §3. Replaces the `opaque` placeholder
`ClosedThresholdValidity` of the FC39-P0 targets (`evidence/fc39-p0/Targets.lean.txt:43–45`). Rule
(dispositions 49, "Threshold slots"): the `Out` of a slot is the FULL analytic conclusion of its
native declaration(s) at the CHOSEN register value — never positivity, a register inequality, "other
thresholds exist", or rows / adapted data / a certificate. The record carries the standing sequence
(task-47 draft §4.2: LPA02's `V`, the common tail and LPA01's radii depend on it).

* `GC.MetricGeometry.Cfs15ModulusOut k K B Ξ`: the conclusion of `cfs15_modulus_row`
  (`Metric/CloudSmoothingModulusRow.lean:30–121`, verbatim) for the GIVEN modulus `Ξ`.
* `Lc09Out σ Λ w M`: the per-member conclusion of LC09 `exists_kl618_metric_model_tail`
  (`RescaledLimits/KL618Tail.lean:54–64`, verbatim) on a normalized member model `M`.
* `ClosedFamilyInstance K R M δ εr Λz`: ONE instance of the final family `LocalChartPacketsC14` on
  the normalized model `M` with EXACTLY the parameters read off the register `R`
  (`StaticRegisterFamilyAdapter`), with LPA01's scale window at `R.w, R.Λ`.
* `ClosedFamilyAt K Wseq gseq R`: the joint `Out` of the producer-bound slots (circleUp, β₂Up, ΔLow,
  errorsUp, sectionUp, lfr29W, endpointUp, scaleUp, wUp, splitUp, β₁Up, T₀Low, lpa02V, tailLow;
  native declaration `eventually_nonempty_localChartPacketsC14`,
  `LocalChartPacketsC14Producer.lean:218–262`) with σcol's `Out` (LC09 at `T.σcol`): one
  `δ, εr < cap, Λz` with `20 Λz ≤ T₀` and, for EVERY member `m ≥ R.later.tail`, a normalized model
  carrying the family at `R` (with `V = R.split.V`, `T = R.split.T₀`) and LC09's conclusion.
* `ClosedThresholdValidity K A Wseq gseq D T`: the early sources (`gafMultiplicity`,
  `cgpProfileBound`, `gafDerivativeBound`, CFS15 at `gafStageDim`), LC18
  (`threeSplittingExclusionThreshold`), `I₁`, LPA01's standing clauses at `α = T.H` (the producer's
  `hstand`, `hder` with `A' = boundaryDerivativeConstant A K`) and the joint package at EVERY
  register.

Fields for slots whose native rows are still open (design §4: early `C`, `Nb`, `cw`, TCP02/TCP04 on
the final family, LFR20/LFR44/LFR35–38/FC22/SGP02, LC73 normal-flow) come in later files.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open DifferentialGeometry DifferentialGeometry.Analysis GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped BigOperators NNReal ContDiff Manifold Topology ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace GC.MetricGeometry

/-- The conclusion of CFS15 (`cfs15_modulus_row`, verbatim) for the given modulus `Ξ`. -/
def Cfs15ModulusOut (k K : ℕ) (B : ℝ) (Ξ : ℝ → ℝ) : Prop :=
  ∃ θ₁ : ℝ, 0 < θ₁ ∧ Tendsto Ξ (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ₁ → (∃ m : ℕ, Ξ Γ = (1 / 2 : ℝ) ^ (m + 4)) ∧
      ((∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
          ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
          δ₀ ≤ (Ξ Γ) / (3 * finiteCloudJetBudget F C K) ∧ Γ ≤ δ₀ ∧
          ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
            [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
            ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
            (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
            ∀ rmin R δ : ℝ, 0 < rmin →
            (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
            0 < δ → δ ≤ δ₀ →
            (∀ x ∈ T, ∀ y ∈ T, dist y x ≤ 128 * (Ξ Γ)⁻¹ * max (r y) (r x) →
              r x / B ≤ r y ∧ r y ≤ B * r x) →
            (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
              ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
                ENNReal.ofReal (δ * r x)) →
            ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
              I.PairwiseDisjoint (fun i => ball i (r i)) ∧
              (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
              ((⋃ x ∈ S, ball x (8 * (Ξ Γ)⁻¹ * r x)) ⊆
                ⋃ i ∈ I, ball i (20 * (Ξ Γ)⁻¹ * r i)) ∧
              let w : H → H → ℝ := fun i y =>
                  ballCutoff i (40 * (Ξ Γ)⁻¹ * r i) (2 * (40 * (Ξ Γ)⁻¹ * r i)) y /
                  (∑ a ∈ hI.toFinset,
                    ballCutoff a (40 * (Ξ Γ)⁻¹ * r a) (2 * (40 * (Ξ Γ)⁻¹ * r a)) y)
              let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
                  Module.End.eigenspace
                  (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
              let η : H → H := fun y => (Q y).starProjection
                (y - ∑ i ∈ hI.toFinset, w i y • i)
              let U : Set H := ⋃ i ∈ I, ball i (20 * (Ξ Γ)⁻¹ * r i)
              let Z : Set H := {z | z ∈ U ∧ η z = 0}
              (IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : U)) ∧
                ∃ cs : ChartedSpace (Fin k → ℝ) Z,
                  let _ := cs
                  IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
                  _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
                    (Subtype.val : Z → H) ∧
                  let V : S → TopologicalSpace.Opens H := fun x => ⟨ball (x : H) (r x), isOpen_ball⟩
                  let Ω : TopologicalSpace.Opens H :=
                    ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
                  ∃ p : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin k → ℝ), Z⟯,
                    _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) ∞ p ∧
                    (∀ z : Ω, IsMinOn (fun y => dist (z : H) y) Z (p z : H) ∧
                      (∀ y ∈ Z, IsMinOn (fun w => dist (z : H) w) Z y → y = (p z : H))) ∧
                    (∀ x : S, ∀ z : V x,
                      ‖(p ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩ : H) -
                        ((x : H) + (P x).starProjection ((z : H) - x))‖ ≤ (Ξ Γ) * r x ∧
                      (let D : H →L[ℝ] H :=
                        mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (p y : H))
                          ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩
                      ‖D - (P x).starProjection‖ ≤ (Ξ Γ))) ∧
                    (let pAmbient : H → H := nearestAmbientExtension Ω Z p
                     ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j : ℕ,
                       ‖iteratedFDeriv ℝ j
                         (fun y => pAmbient y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
                           C j * δ * r x * ((r x)⁻¹) ^ j) ∧
                    (let pAmbient : H → H := nearestAmbientExtension Ω Z p
                     ∀ x : S, ∀ z ∈ ball (x : H) (r x), ∀ j ≤ K,
                       ‖iteratedFDeriv ℝ j
                         (fun y => pAmbient y - ((x : H) + (P x).starProjection (y - x))) z‖ ≤
                           ((Ξ Γ) / 3) * r x * ((r x)⁻¹) ^ j) ∧
                    (∀ z : Z, ∀ hz : (z : H) ∈ Ω, p ⟨(z : H), hz⟩ = z) ∧
                    (∀ x : S, ∀ z : Z, (z : H) ∈ ball (x : H) (r x) →
                      ‖actualZeroSetNormalProjector k Z z - (P x)ᗮ.starProjection‖ ≤ (Ξ Γ))) ∧
              (let N : Set H := ⋃ x ∈ S, ball x (r x);
                IsProperMap (Subtype.val : {z : N | (z : H) ∈ Z} → N)) ∧
              (Z ⊆ ⋃ q ∈ T, ball q ((Ξ Γ) * r q)) ∧
              (∀ x ∈ S,
                hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ closedBall 0 (Ξ Γ)⁻¹)
                    (((fun y => (r x)⁻¹ • (y - x)) '' Z) ∩ closedBall 0 (Ξ Γ)⁻¹) ≤
                    ENNReal.ofReal (7 * (Ξ Γ) / 16) ∧
                  hausdorffEDist (((fun y => (r x)⁻¹ • (y - x)) '' T) ∩ ball 0 (Ξ Γ)⁻¹)
                    (((fun y => (r x)⁻¹ • (y - x)) '' Z) ∩ ball 0 (Ξ Γ)⁻¹) ≤
                    ENNReal.ofReal (7 * (Ξ Γ) / 16)) ∧
              ∃ g : ∀ x : S, P x → (P x)ᗮ, ∀ x : S,
                ContDiffOn ℝ ∞ (g x) (ball 0 (4 * (Ξ Γ)⁻¹ * r x)) ∧
                (∀ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x), ‖g x t‖ ≤ r x / 4 ∧
                  (x : H) + orthogonalCoordinateSum (P x) (t, g x t) ∈ Z) ∧
                (∀ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x),
                  ∀ n ∈ closedBall (0 : (P x)ᗮ) (r x),
                  η ((x : H) + orthogonalCoordinateSum (P x) (t, n)) = 0 ↔ n = g x t) ∧
                (∀ m t, t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x) → ∀ j, j ≤ m →
                  ‖iteratedFDeriv ℝ j (g x) t‖ ≤ F m * δ * r x * ((r x)⁻¹) ^ j) ∧
                Z ∩ ball (x : H) (3 * (Ξ Γ)⁻¹ * r x) =
                  {z : H | ∃ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x),
                    z = (x : H) + orthogonalCoordinateSum (P x) (t, g x t)} ∩
                      ball (x : H) (3 * (Ξ Γ)⁻¹ * r x) ∧
                (∀ t ∈ ball (0 : P x) (4 * (Ξ Γ)⁻¹ * r x), ∀ j ≤ K + 1,
                  ‖iteratedFDeriv ℝ j (g x) t‖ ≤ ((Ξ Γ) / 3) * r x * ((r x)⁻¹) ^ j)))

/-- `cfs15_modulus_row` supplies a modulus with `Cfs15ModulusOut` (the definition is its
conclusion). -/
theorem exists_cfs15ModulusOut_VAL (k K : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ Ξ : ℝ → ℝ, Cfs15ModulusOut k K B Ξ := by
  obtain ⟨θ₁, hθ₁, Ξ, hΞ, h⟩ := cfs15_modulus_row.{0} k K B hB
  exact ⟨Ξ, θ₁, hθ₁, hΞ, h⟩

end GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry

universe u

/-- The per-member conclusion of LC09 (`exists_kl618_metric_model_tail`, verbatim) on a normalized
model: every scale `ρ` of LPA01's window at `w, Λ` sees a `σ`-close metric model. -/
def Lc09Out (σ Λ w : ℝ) {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    (M : ClosedModel W g) : Prop :=
  ∀ (p : M.X) (ρ : ℝ) (hρ : 0 < ρ), firstVolumeScale M.gX p w / 2 ≤ ρ →
    ρ ≤ 2 * firstVolumeScale M.gX p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) →
    ∃ (Y : Type) (mY : MetricSpace Y),
      letI := mY
      ∃ q : Y, CompleteSpace Y ∧ ProperSpace Y ∧ dimH (univ : Set Y) ≤ 2 ∧
        fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        Nonempty (@KleinerLottApprox M.X Y (M.mX.rescale ρ⁻¹ (inv_pos.mpr hρ)) mY p q
          σ)

/-- **Consumer (verbatim check of `Lc09Out`)**: LC09 on any sequence of normalized member models
with LPA01's standing curvature inequality gives `Lc09Out` on a tail. -/
theorem eventually_lc09Out_VAL {σ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) (hΛ : 0 < Λ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (Wseq : ℕ → CompactCarrier.{u})
        (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
        (M : ∀ m, ClosedModel (Wseq m) (gseq m)) (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ m (p : (M m).X), ENNReal.ofReal (α m * firstVolumeScale (M m).gX p (α m)⁻¹) ≤
          curvatureRadius (M m).gX p) →
        ∀ᶠ m in atTop, Lc09Out σ Λ w (M m) := by
  obtain ⟨w₀, hw₀, h⟩ := exists_kl618_metric_model_tail (I := 𝓘(ℝ, E3))
    finrank_euclideanSpace_fin hσ hσ1 hΛ
  exact ⟨w₀, hw₀, fun w hw hww hwc Wseq gseq M α hα hst =>
    h w hw hww hwc (fun m => (M m).X) (fun m => (M m).gX) (fun m => (M m).hmetric) α hα hst⟩

/-- **One instance of the final family at the register `R`** on a normalized member model: the scale
`ρ` in LPA01's window at `R.w, R.Λ` and `LocalChartPacketsC14` with exactly the parameters read off
`R`. -/
structure ClosedFamilyInstance (K : ℕ) {D : ClosedEarlyData} {T : ClosedThresholds D}
    (R : ClosedRegister D T) {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    (M : ClosedModel W g) (δ εr Λz : ℝ) where
  /-- The scale. -/
  ρ : M.X → ℝ
  ρ_pos : ∀ p, 0 < ρ p
  /-- LPA01's window (C14P:259–260). -/
  ρ_bounds : ∀ p, firstVolumeScale M.gX p R.later.scale.w / 2 < ρ p ∧
    ρ p < 2 * firstVolumeScale M.gX p (closedWPrime R.later.scale)
  /-- The final family at `R`. -/
  family : LocalChartPacketsC14 M.X M.gX M.hmetric ρ ρ_pos R.later.scale.Λ R.famβ R.later.excl.Δ
    R.famσs K R.famσc R.later.err.μ R.later.split.b R.fams R.famb' R.fams' R.famε R.famγc R.famβc
    R.famLmax R.later.err.τ R.later.circle.γ δ εr R.later.err.e₀ R.later.split.T₀ R.later.split.V
    R.later.err.ve R.famζ Λz

/-- **The joint `Out` of the producer-bound closed slots at `R`** (with σcol's LC09 `Out`): ONE `δ`,
ONE zero radial difference-Lipschitz constant `εr < cap`, ONE shell ratio `Λz` with `20 Λz ≤ T₀`,
and on EVERY member from the register's tail on, a normalized model carrying the family at `R` and
LC09 at `T.σcol`. -/
def ClosedFamilyAt (K : ℕ) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier) {D : ClosedEarlyData}
    {T : ClosedThresholds D} (R : ClosedRegister D T) : Prop :=
  ∃ δ εr Λz : ℝ, 0 < δ ∧ 0 < εr ∧ εr < R.famCap ∧ 0 < Λz ∧ 20 * Λz ≤ R.later.split.T₀ ∧
    ∀ m, R.later.tail ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m),
      Nonempty (ClosedFamilyInstance K R M δ εr Λz) ∧
        Lc09Out T.σcol R.later.scale.Λ R.later.scale.w M

/-- **The closed threshold validity** (review 49, B.1): every slot of `ClosedThresholds` bound to
the analytic conclusion of its native declaration at the chosen register value, on the given
standing sequence. -/
structure ClosedThresholdValidity (K : ℕ) (A : ℝ → ℝ) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (D : ClosedEarlyData) (T : ClosedThresholds D) : Prop where
  /-- PR01 `N`: GAF01's multiplicity `⌊fc07ActiveBound⌋₊` (every active-tag count of `𝓔⁰`). -/
  N_ge : gafMultiplicity ≤ D.N
  /-- PR01 `P`: CGP02's profile bound. -/
  P_ge : cgpProfileBound ≤ D.P
  /-- PR02 `L₀`: CGP02's global derivative bound. -/
  L₀_ge : gafDerivativeBound ≤ D.L₀
  /-- PR03 `Ξ_j`: CFS15's full conclusion for the chosen modulus at the stage dimension `k_j`, jet
  order `K`, ratio `B = 5/3` (GAF01, `ActualAdjustmentChoice.lean:96`). -/
  Ξ_cfs15 : ∀ j, Cfs15ModulusOut (gafStageDim j) K (5 / 3) (D.Ξ j)
  /-- PR12 `lc18`: LC18's obstruction (the producer's `β 3 ≤ thr`, C14P:240). -/
  lc18_le : T.lc18 ≤ threeSplittingExclusionThreshold.{0, 0}
  /-- PR20 `I₁`: the comparison constant of `v_* = w'/(24 I(1))` (LPA01/LPA02's volume constant). -/
  I₁_eq : T.I₁ = ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2
  /-- PR24 `H`: LPA01's standing clauses at `α = T.H` (the producer's `hstand`, `hder`,
  C14P:249–255, with `A' = boundaryDerivativeConstant A K`) on every member. -/
  standing : ∀ m (p : (Wseq m).Carrier),
    ENNReal.ofReal (T.H m * firstVolumeScale (gseq m) p (T.H m)⁻¹) ≤ curvatureRadius (gseq m) p ∧
    ∀ v, 0 < v → v < 4 * Real.pi / 3 → (T.H m)⁻¹ ≤ v → ∀ C, 0 < C → C < T.H m → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (gseq m) p (C * firstVolumeScale (gseq m) p v),
        curvatureDerivativeNorm (gseq m) k y ≤
          boundaryDerivativeConstant A K C v * (firstVolumeScale (gseq m) p v ^ (k + 2))⁻¹
  /-- PR11–PR25: the joint package of the producer-bound slots at EVERY register (closed members).
  -/
  family : (∀ m, ClosedMemberFacts (Wseq m)) →
    ∀ R : ClosedRegister D T, ClosedFamilyAt K Wseq gseq R

namespace ClosedThresholdValidity

variable {K : ℕ} {A : ℝ → ℝ} {Wseq : ℕ → CompactCarrier.{u}}
  {gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier}
  {D : ClosedEarlyData} {T : ClosedThresholds D}

/-- **Consumer (wrapper (1) shape, family level)**: at every register, one tail `N ≥ R.later.tail`
on which every member carries the final family at `R`. -/
theorem exists_family_on_tail_VAL (hv : ClosedThresholdValidity K A Wseq gseq D T)
    (hf : ∀ m, ClosedMemberFacts (Wseq m)) (R : ClosedRegister D T) :
    ∃ N : ℕ, R.later.tail ≤ N ∧ ∃ δ εr Λz : ℝ, ∀ m, N ≤ m →
      ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty (ClosedFamilyInstance K R M δ εr Λz) := by
  obtain ⟨δ, εr, Λz, -, -, -, -, -, h⟩ := hv.family hf R
  exact ⟨R.later.tail, le_rfl, δ, εr, Λz, fun m hm => (h m hm).imp fun _ hM => hM.1⟩

/-- **Consumer (the adapters at work)**: the standing clauses transported to ANY normalized model of
a member — exactly the producer's `hstand` and `hder` on the model sequence. -/
theorem standing_on_model_VAL (hv : ClosedThresholdValidity K A Wseq gseq D T) (m : ℕ)
    (M : ClosedModel (Wseq m) (gseq m)) (p : M.X) :
    ENNReal.ofReal (T.H m * firstVolumeScale M.gX p (T.H m)⁻¹) ≤ curvatureRadius M.gX p ∧
    ∀ v, 0 < v → v < 4 * Real.pi / 3 → (T.H m)⁻¹ ≤ v → ∀ C, 0 < C → C < T.H m → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf M.gX p (C * firstVolumeScale M.gX p v),
        curvatureDerivativeNorm M.gX k y ≤
          boundaryDerivativeConstant A K C v * (firstVolumeScale M.gX p v ^ (k + 2))⁻¹ := by
  obtain ⟨h1, h2⟩ := hv.standing m (M.ψ p)
  refine ⟨by rw [M.firstVolumeScale_eq, M.curvatureRadius_eq]; exact h1, ?_⟩
  intro v hv0 hvc hvH C hC hCH k hk y hy
  rw [M.ball_eq_preimage, M.firstVolumeScale_eq] at hy
  rw [M.curvatureDerivativeNorm_eq, M.firstVolumeScale_eq]
  exact h2 v hv0 hvc hvH C hC hCH k hk (M.ψ y) hy

/-- **Consumer**: the splitting coordinate `β 3 = β₃` of the family at `R` is below LC18's
obstruction. -/
theorem famβ_three_le_VAL (hv : ClosedThresholdValidity K A Wseq gseq D T)
    (R : ClosedRegister D T) : R.famβ 3 ≤ threeSplittingExclusionThreshold.{0, 0} := by
  rw [ClosedRegister.famβ_three_VAL]
  exact (R.later.β₃_lt.trans_le hv.lc18_le).le

end ClosedThresholdValidity

/-- **The H slot is bindable now** (PBR03, B:10298–10328): on the closed standing sequence,
`H m = m + 2` satisfies the standing clauses — `closed_lc09_standing_of_closedCollapseHypotheses`
(SC:183) and `closed_reduce_of_closedCollapseHypotheses` (SC:157) at the ratio `w_{m+2}`. -/
theorem closed_standing_clauses_VAL (K : ℕ) (A : ℝ → ℝ) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)))
    (m : ℕ) (p : (Wseq m).Carrier) :
    ENNReal.ofReal (((m : ℝ) + 2) * firstVolumeScale (gseq m) p ((m : ℝ) + 2)⁻¹) ≤
      curvatureRadius (gseq m) p ∧
    ∀ v, 0 < v → v < 4 * Real.pi / 3 → ((m : ℝ) + 2)⁻¹ ≤ v → ∀ C, 0 < C → C < (m : ℝ) + 2 →
      ∀ k ≤ K, ∀ y ∈ riemannianBallOf (gseq m) p (C * firstVolumeScale (gseq m) p v),
        curvatureDerivativeNorm (gseq m) k y ≤
          boundaryDerivativeConstant A K C v * (firstVolumeScale (gseq m) p v ^ (k + 2))⁻¹ := by
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  refine ⟨?_, ?_⟩
  · have h := closed_lc09_standing_of_closedCollapseHypotheses (n := m + 2) (by omega) (hg m) p
    rwa [hcast] at h
  · intro v _ hvc hvH C _ hCH k hk y hy
    have hvH' : ((m + 2 : ℕ) : ℝ)⁻¹ ≤ v := by rwa [hcast]
    have hCH' : C < ((m + 2 : ℕ) : ℝ) := by rwa [hcast]
    exact closed_reduce_of_closedCollapseHypotheses (n := m + 2) (by omega) (hg m) p hCH' hvH'
      (by unfold euclideanThreeUnitBallVolume; exact hvc) k hk y hy

end DifferentialGeometry.Geometry.Collapse
