import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.JointZeroPacketAssembled
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA02SequenceBinding
import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformJointScale
import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformJointScaleConeRadial
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.BufferedRadialFunctionAtScale
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry

/-!
# LPA02 (row): uniform joint zero witnesses from the finite category

Frozen blueprint master207A, LPA02 (A:30349): in LPA01, EVERY sequence `α_i → ∞`, `p_i ∈ M^{α_i}`
has a subsequence with the finite package of LFR14, LFR49 and LFR59; consequently, for fixed
`δ, ε, e, T` in LC57's ranges, there are `V ≥ T` and `α₀` such that every `α > α₀` and every centre
has ONE scale `s ∈ [T, V]`, model, cone, selected radial function (with LC67's enlarged buffer) and
matching core (open-ball types).

`lpa02_uniform_joint_zero_witnesses` is this row for LPA01's standing data (closed smooth
three-manifolds with aligned metrics, `α → ∞`, the LC02 standing bound, the (LPA.1) derivative
bounds `K, A`), in GAP D's shape (`exists_uniform_scale_zero_model_data`) WITHOUT GAP C's `hmodel`.
It is uniform in the normalizing radius: on one tail, at EVERY point `p` and EVERY radius
`0 < r ≤ 2 r_p(w')` (`w' = w / (2(1 + 2Λ⁻¹)³)`, LPA01's upper bound of the LC02 scale) there is
`s ∈ [T, V]` with, at the scale `s r`:
* one complete nonnegatively curved `C^{K-1}` model `(N, G, q)` (proper, connected, four-point
  comparison `0`, metric segments) with its LFR59 cone `(C, o)` (proper, radial cone data,
  Kleiner–Lott maps from every blow-down) and a SMOOTH manifold `Ns ≃ₜ N`;
* the original curvature buffer `sec ≥ -(1/60)² (s r)⁻²` on `B(p, 400 s r)`;
* a Kleiner–Lott `δ`-map of `(X, (s r)⁻¹ d, p)` to `(C, o)` with `δ < δ'`;
* LC67's radial function at the scale `s r` (all LC30 clauses, smooth near `{3/40 ≤ d ≤ 11}`) with
  LC31's cutoff;
* every open ball `B(p, ρ' s r)`, `ρ' ∈ [1/5, 2]`, diffeomorphic to `Ns` (LFR49 item (3), both
  branches; LC61's identification).

Proof: the LC58 kernel `exists_uniform_scale_interval_of_eventual_witnesses` on the pairs
`(p, r)`. Its sequential hypothesis is the first paragraph of LPA02's proof: for any sequence of
pairs the normalized sources satisfy LFR14's eventual hypotheses (`lpa02_normalized_sequence_hypotheses`);
LFR49's `lfr49_finite_model_ball_type_all_scales` (rescaled sources) gives the model, `Ns` and the
ball types at every large scale; LFR59 (`exists_finite_cone_package_of_limit`) the cone; LC57 (1)
(`exists_scale_eventually_normalized_cone_radial_witnesses`) the Kleiner–Lott maps. The buffer
comes from LPA01's normalized curvature clause once `α > 1600 V`; LC67/LC31 are then attached at
the chosen scale (`exists_buffered_radial_cutoff_at_scale`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **LPA02 (row).** For LPA01's standing data (`10 ≤ K`) and LC57's ranges `0 < ε < 1`,
`δ' > 0`, `0 < e < 1/40`, `T` fixed first: there are `V ≥ T`, one cone error `0 < δ < δ'` and a
tail on which every point `p` and every radius `0 < r ≤ 2 r_p(w')` have a scale `s ∈ [T, V]`, one
complete nonnegative `C^{K-1}` model `(N, G, q)` with its cone `(C, o)` and a smooth `Ns ≃ₜ N`,
the original buffer on `B(p, 400 s r)`, a Kleiner–Lott `δ`-map at the scale `s r`, LC67's radial
function with LC31's cutoff, and `B(p, ρ' s r) ≃ Ns` for every `ρ' ∈ [1/5, 2]`. -/
theorem lpa02_uniform_joint_zero_witnesses
    {X : ℕ → Type} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
    [∀ i, IsManifold I3 ∞ (X i)] [∀ i, CompactSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v)
    (hder : ∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
        curvatureDerivativeNorm (g i) k y ≤
          A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3)
    {ε δ' e T : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ' : 0 < δ') (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop, ∀ (p : X i) (r : ℝ) (hr : 0 < r),
      r ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) →
      ∃ s ∈ Icc T V, ∃ hs : 0 < s,
      ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace E3 N),
        letI := mN
        letI := cN
        ∃ (_ : IsManifold I3 ∞ N)
          (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : N → Type _))
          (q : N),
          ProperSpace N ∧ ConnectedSpace N ∧
          (letI : RiemannianBundle (fun x : N => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
           IsRiemannianManifold I3 N) ∧
          (∀ (x : N) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
          fourPointComparison 0 (univ : Set N) ∧
          (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
            f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂) ∧
          ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
            ProperSpace C ∧
            (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
              Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
          ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
            (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N),
            (∀ y ∈ Metric.ball p (400 * (s * r)),
              SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (s * r)⁻¹ ^ 2))) ∧
            Nonempty (@KleinerLottApprox (X i) C
              ((mX i).rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))) mC p o δ) ∧
            (letI := (mX i).rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))
            let gR := scaleMetric ((s * r)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (mul_pos hs hr)) 2) (g i)
            ∃ F : X i → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
              (∃ O : Set (X i), IsOpen O ∧ {x : X i | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O) ∧
              (∀ x, |F x - Metric.infDist x {p}| < e) ∧
              (∀ x, x ∉ {x : X i | 1 / 20 < dist x p ∧ dist x p < 20} →
                F x = Metric.infDist x {p}) ∧
              (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
                ε * dist x y) ∧
              (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
              (∀ q' ∈ {x : X i | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
                1 - ε ≤ Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ∧
                  Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ≤ 1 + ε) ∧
              (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
              F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : X i | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
              (∃ O' : Set (X i), IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q' ∈ O', gradFun gR F q' ≠ 0) ∧
              ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
                ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
                (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
                (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
                tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
                  {x : X i | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
                ∀ q', Real.sqrt (gR.inner q'
                  (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')
                  (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')) ≤ L * (1 + ε)) ∧
            ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (X i) Ns ∞,
              Ψ.source = Metric.ball p (ρ' * (s * r)) ∧ Ψ.target = univ := by
  have instNZ_LPA02 : NeZero (Module.finrank ℝ E3) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  obtain ⟨δ, hδ0, hδ1, hδδ', hδr⟩ := exists_coneError_below_thresholds hε hδ'
  -- the LC58 kernel on the pairs `(p, r)` with `0 < r ≤ 2 r_p(w')`
  obtain ⟨V, hTV, α₀, hGC⟩ := exists_uniform_scale_interval_of_eventual_witnesses
    (X := fun i => {pr : X i × ℝ //
      0 < pr.2 ∧ pr.2 ≤ 2 * firstVolumeScale (g i) pr.1 (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))})
    (fun i y s => ∃ hs : 0 < s,
      ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace E3 N),
        letI := mN
        letI := cN
        ∃ (_ : IsManifold I3 ∞ N)
          (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : N → Type _))
          (q : N),
          ProperSpace N ∧ ConnectedSpace N ∧
          (letI : RiemannianBundle (fun x : N => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
           IsRiemannianManifold I3 N) ∧
          (∀ (x : N) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
          fourPointComparison 0 (univ : Set N) ∧
          (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
            f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂) ∧
          ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
            ProperSpace C ∧
            (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
              Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
          ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
            (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N),
            Nonempty (@KleinerLottApprox (X i) C
              ((mX i).rescale (s * y.1.2)⁻¹ (inv_pos.mpr (mul_pos hs y.2.1))) mC y.1.1 o δ) ∧
            ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (X i) Ns ∞,
              Ψ.source = Metric.ball y.1.1 (ρ' * (s * y.1.2)) ∧ Ψ.target = univ) T
    (by
      intro a ha z
      -- LPA02, first paragraph: LFR14's hypotheses for the normalized sequence
      obtain ⟨hmetric', hv0, hvol', hcurv', hη, hL, hsec'⟩ :=
        lpa02_normalized_sequence_hypotheses (finrank_euclideanSpace_fin) g hmetric hα hstand K A
          hA hder hΛ hw hwc a ha (fun j => (z j).1.1) (fun j => (z j).1.2) (fun j => (z j).2.1)
          (fun j => (z j).2.2)
      -- LFR49 (T0′) on the rescaled sources
      obtain ⟨k, hk, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hGH, _, _, _, -, -, Ns,
          tNs, cNs, hNs, hhom, R₃, h3⟩ :=
        @lfr49_finite_model_ball_type_all_scales K hK 1 _ one_pos hv0
          (fun R => (2 : ℝ) ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
          (fun j => X (a j))
          (fun j => (mX (a j)).rescale ((z j).1.2)⁻¹ (inv_pos.mpr (z j).2.1))
          (fun j => (inferInstance : ChartedSpace E3 (X (a j))))
          (fun j => (inferInstance : IsManifold I3 ∞ (X (a j))))
          (fun j => (inferInstance : SigmaCompactSpace (X (a j))))
          (fun j => ((mX (a j)).rescale_completeSpace_iff _ _).mpr inferInstance)
          (fun j => connectedSpace_of_aligned_metric (g (a j)) (hmetric (a j)) (z j).1.1)
          (fun j => normalizedCenterMetric (g (a j)) ((z j).1.2) (z j).2.1) hmetric'
          (fun j => (z j).1.1) hvol' hcurv' _ _ hη hL hsec'
      -- LFR59: the cone of the SAME model, with its properness
      obtain ⟨C, mC, o, ⟨Hc⟩, hCp, -, -, hcone⟩ :=
        exists_finite_cone_package_of_limit (by omega : 3 ≤ K) G hRiem hsecG q
      -- the model clauses: four-point comparison and segments
      let instRB_LPA02 : RiemannianBundle (fun x : N => TangentSpace I3 x) :=
        ⟨G.toRiemannianMetric⟩
      have instRM_LPA02 : IsRiemannianManifold I3 N := hRiem
      have hGnorm : ∀ (x : N) (u : TangentSpace I3 x),
          ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x u u)) := by
        intro x u
        rw [← ofReal_norm, norm_eq_sqrt_real_inner]
        rfl
      have hn : (2 : ℕ∞ω) ≤ ((K - 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 2 ≤ K - 1 by omega)
      have hfour : fourPointComparison 0 (univ : Set N) :=
        DifferentialGeometry.Geometry.FiniteComparison.fourPointComparison_zero_univ_finite G hn
          hGnorm hsecG
      have hseg : ∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
          f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂ :=
        fun x y => Metric.exists_metric_segment_of_approximate_midpoints
          (DifferentialGeometry.Geometry.FiniteComparison.approximate_midpoints_finite G hn hGnorm)
          x y
      -- LFR49 step 1 along `k`, in the `scaleMetric` form of LC57
      obtain ⟨Hb, hHb, hsecM⟩ := @exists_curvature_scale_along_of_eventual (fun j => X (a j))
        (fun j => (mX (a j)).rescale ((z j).1.2)⁻¹ (inv_pos.mpr (z j).2.1))
        (fun j => (inferInstance : ChartedSpace E3 (X (a j))))
        (fun j => (inferInstance : IsManifold I3 ∞ (X (a j))))
        (fun j => normalizedCenterMetric (g (a j)) ((z j).1.2) (z j).2.1) hmetric'
        (fun j => (z j).1.1) _ _ hη hL hsec' k hk
      have hsecS : ∀ j, ∀ y ∈ @Metric.ball (X (a (k j)))
          ((mX (a (k j))).rescale ((z (k j)).1.2)⁻¹
            (inv_pos.mpr (z (k j)).2.1)).toPseudoMetricSpace ((z (k j)).1.1) (Hb j),
          SectionalBoundedBelowAt (scaleMetric (((z (k j)).1.2)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (z (k j)).2.1) 2) (g (a (k j)))) y (-((Hb j)⁻¹ ^ 2)) := by
        intro j y hy
        rw [← normalizedCenterMetric_eq_scaleMetric]
        exact hsecM j y hy
      -- LC57 (1): Kleiner–Lott maps at every large scale
      obtain ⟨R₀, hR₀, hall⟩ := exists_scale_eventually_normalized_cone_radial_witnesses
        (M := fun j => X (a (k j))) (fun j => g (a (k j))) (fun j => hmetric (a (k j)))
        (fun j => (z (k j)).1.2) (fun j => (z (k j)).2.1) hGH Hc hcone Hb hHb hsecS
        hδ0 hδ1 hε hε1 he he1
      have hR0 : R₀ ≤ max (max R₀ R₃) T := (le_max_left _ _).trans (le_max_left _ _)
      have hR3 : R₃ ≤ max (max R₀ R₃) T := (le_max_right _ _).trans (le_max_left _ _)
      have hR : 0 < max (max R₀ R₃) T := hR₀.trans_le hR0
      refine ⟨k, hk, max (max R₀ R₃) T, le_max_right _ _, ?_⟩
      filter_upwards [hall _ hR hR0, h3 _ hR3] with j hj1 hj3
      refine ⟨hR, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o, ⟨Hc⟩,
        hCp, hcone, Ns, tNs, cNs, hNs, hhom, hj1.1, fun ρ' hρ' => ?_⟩
      obtain ⟨Ψ, hΨs, hΨt⟩ := hj3 ρ' hρ'
      refine ⟨Ψ, ?_, hΨt⟩
      rw [hΨs]
      ext x
      change ((z (k j)).1.2)⁻¹ * dist x (z (k j)).1.1 < ρ' * max (max R₀ R₃) T ↔
        dist x (z (k j)).1.1 < ρ' * (max (max R₀ R₃) T * (z (k j)).1.2)
      rw [inv_mul_lt_iff₀ (z (k j)).2.1]
      have hcomm : (z (k j)).1.2 * (ρ' * max (max R₀ R₃) T) =
          ρ' * (max (max R₀ R₃) T * (z (k j)).1.2) := by ring
      rw [hcomm])
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [eventually_gt_atTop α₀,
    eventually_simultaneous_analytic_data (finrank_euclideanSpace_fin) g hmetric hα hstand K A hA
      hder hΛ hw hwc,
    hα.eventually_gt_atTop (1600 * V)] with i hiα hdata hαV p r hr hrv
  obtain ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o,
      ⟨Hc⟩, hCp, hcone, Ns, tNs, cNs, hNs, hhom, ⟨φ⟩, h3⟩ := hGC i hiα ⟨(p, r), hr, hrv⟩
  -- the original buffer from LPA01's normalized curvature clause (`α > 1600 V`)
  have hbuf : ∀ y ∈ Metric.ball p (400 * (s * r)),
      SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (s * r)⁻¹ ^ 2)) := by
    intro y hy
    have hsV : s ≤ V := hsI.2
    have hαs : 1600 * s < α i := by linarith
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric (g i) r hr) p (α i / 4) := by
      change riemannianEDistOf (normalizedCenterMetric (g i) r hr) p y < ENNReal.ofReal (α i / 4)
      rw [riemannianEDistOf_normalizedCenterMetric (g i) (hmetric i) hr, MetricSpace.rescale_dist]
      have hd : dist p y < 400 * (s * r) := by rw [dist_comm]; exact Metric.mem_ball.mp hy
      have hlt : r⁻¹ * dist p y < α i / 4 := by
        rw [inv_mul_lt_iff₀ hr]
        nlinarith
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hlt
    have h := (hdata.2.2.2 p r hr hrv).2.2.1 y hy'
    rw [normalizedCenterMetric_eq_scaleMetric, sectionalBoundedBelowAt_scaleMetric_iff] at h
    refine h.mono ?_
    have h60 : 60 * s ≤ α i / 4 := by linarith
    have hsq : ((α i / 4) ^ 2)⁻¹ ≤ ((60 * s) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h60 2)
    have hid : (1 / 60) ^ 2 * (s * r)⁻¹ ^ 2 = ((60 * s) ^ 2)⁻¹ * r⁻¹ ^ 2 := by
      ring
    rw [hid, neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  exact ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o,
    ⟨Hc⟩, hCp, hcone, Ns, tNs, cNs, hNs, hhom, hbuf, ⟨φ⟩,
    exists_buffered_radial_cutoff_at_scale (g i) (hmetric i) (mul_pos hs hr) φ Hc hbuf hε hε1 hδr
      he he1, h3⟩

end DifferentialGeometry.Geometry.Collapse
