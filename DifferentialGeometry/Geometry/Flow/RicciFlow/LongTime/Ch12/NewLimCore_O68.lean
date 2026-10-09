import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HAnchor_O60

set_option autoImplicit false

/-! # CH12-O68 G1: regular-time limit for the `hNewLim` binder of `hanchor_O60`

From the LTF05a compactness body (`hcpt`) and `hthickW` (thickW_shape_O40 body): a sequence of
admissible maps `q m` at regular times `t m → ∞` whose basepoint images escape every old core
yields, after a subsequence, a w-thick ESC late sequence `S'` (points `q m bp`) converging to a
hyperbolic `H'`, and maps `ψ m = sliceApprox_O32 S' H' Φ m` (convergence by `hconvS_O32`). -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.CheegerGromovCompactness
open TopologicalSpace Filter
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace GC.LongTime.Ch12

/-- Curvature radius and ball volume of a scaled metric transported along a stage equality. -/
theorem thickTransport_O68 {A B : OrientedThreeStage.{u}} (h : A = B) (mA : A.Metric)
    (mB : B.Metric) (hm : HEq mA mB) (c : ℝ) (hc hc' : 0 < c) (x : A.Carrier) (r : ℝ) :
    curvatureRadius (scaleMetric c hc mB) (cast (congrArg (fun Q : OrientedThreeStage.{u} =>
        Q.Carrier) h) x) = curvatureRadius (scaleMetric c hc' mA) x ∧
      ballVolume (scaleMetric c hc mB) (cast (congrArg (fun Q : OrientedThreeStage.{u} =>
        Q.Carrier) h) x) r = ballVolume (scaleMetric c hc' mA) x r := by
  subst h
  obtain rfl := eq_of_heq hm
  exact ⟨rfl, rfl⟩

/-- `[FROZEN] CH12-O68` G1: regular-time limit + convergence maps + ESC + thickness. -/
theorem newLimCore_O68 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (wstar : ℝ)
    (old : ℕ) (Hold : Fin old → FiniteVolumeHyperbolicModel.{u}) (sold : Fin old → ℝ)
    (mold : ∀ i (t : ℝ), sold i ≤ t → (Hold i).Carrier → (postStage F.observation t).Carrier)
    (hw : 0 < wstar)
    (hcpt : 0 < wstar → ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S wstar →
      ∃ σ : ℕ → ℕ, ∃ hσ : StrictMono σ, ∃ M : FiniteVolumeHyperbolicModel.{u},
        PointedSmoothConverges_S13 (S.subsequence σ hσ) M)
    (hthickW :
      ∃ (ε₀ R₀ T₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ ∃ hT₀ : 0 < T₀,
        ∀ (s : ℝ) (hs : T₀ ≤ s) (q : H.Carrier → (postStage F.observation s).Carrier) (R'' : ℝ),
          R₀ ≤ R'' →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ q (riemannianBallOf H.metric H.basepoint (4 * R'')) →
          (∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
            ckErr_S45 H (postMetric F.observation s) s⁻¹ q k'' p < ε₀) →
          ∀ y ∈ riemannianBallOf H.metric H.basepoint (4 * R''), ∃ r : ℝ, 0 < r ∧
            curvatureRadius (scaleMetric s⁻¹ (inv_pos.mpr (lt_of_lt_of_le hT₀ hs))
              (postMetric F.observation s)) (q y) = ENNReal.ofReal r ∧
            ENNReal.ofReal (wstar * r ^ 3) ≤ ballVolume (scaleMetric s⁻¹
              (inv_pos.mpr (lt_of_lt_of_le hT₀ hs)) (postMetric F.observation s)) (q y) r) :
    ∃ (ε₀ R₀ : ℝ) (k₀ : ℕ), 0 < ε₀ ∧ 0 < R₀ ∧
      ∀ (t : ℕ → ℝ), Filter.Tendsto t Filter.atTop Filter.atTop →
      (∀ m, ∃ s : RegularSlice F.observation, s.time = t m) →
      ∀ (q : (m : ℕ) → H.Carrier → (postStage F.observation (t m)).Carrier),
      (∀ m, ∃ R'' : ℝ, R₀ ≤ R'' ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (q m) (riemannianBallOf H.metric H.basepoint (4 * R'')) ∧
        ∀ k'' : ℕ, k'' ≤ k₀ → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * R''),
          ckErr_S45 H (postMetric F.observation (t m)) (t m)⁻¹ (q m) k'' p < ε₀) →
      (∀ (i : Fin old) (ρ : ℝ), ∃ M : ℕ, ∀ m, M ≤ m → ∀ hi : sold i ≤ t m,
        q m H.basepoint ∉ mold i (t m) hi '' riemannianBallOf (Hold i).metric (Hold i).basepoint ρ) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ (H' : FiniteVolumeHyperbolicModel.{u}) (S' : LatePointSequence_S13 F),
        IsWThickSequence_S13 S' wstar ∧ PointedSmoothConverges_S13 S' H' ∧
        (∀ (i : Fin old) (R : ℝ), ∃ J : ℕ, ∀ j, J ≤ j → ∀ hj : sold i ≤ (S'.slices j).time,
          S'.point j ∉ sliceCast_CX4 (S'.slices j) ''
            (mold i _ hj '' riemannianBallOf (Hold i).metric (Hold i).basepoint R)) ∧
        ∃ ψ : (m : ℕ) → H'.Carrier → (postStage F.observation (t (σ m))).Carrier,
          (∀ m, ψ m H'.basepoint = q (σ m) H.basepoint) ∧
          (∀ (δ r : ℝ) (m' : ℕ), 0 < δ → 0 < r → ∃ I : ℕ, ∀ m, I ≤ m →
            ∃ U : TopologicalSpace.Opens H'.Carrier,
              riemannianBallOf H'.metric H'.basepoint r ⊆ U ∧
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ m) U ∧
              IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => ψ m x) ∧
              ∀ k : ℕ, k ≤ m' → ∀ p ∈ riemannianBallOf H'.metric H'.basepoint r,
                ckErr_S45 H' (postMetric F.observation (t (σ m))) (t (σ m))⁻¹ (ψ m) k p < δ) := by
  obtain ⟨εT, RT, TT, kT, hεT, hTT, hthick⟩ := hthickW
  refine ⟨εT, max RT 1, kT, hεT, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro t ht hreg
  choose s hs using hreg
  obtain rfl : t = fun m => (s m).time := funext fun m => (hs m).symm
  intro q hgood hesc
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop TT)
  let S : LatePointSequence_S13 F :=
    { slices := fun j => s (j + M₀)
      times_tendsto := ht.comp (Filter.tendsto_add_atTop_nat M₀)
      point := fun j => sliceCast_CX4 (s (j + M₀)) (q (j + M₀) H.basepoint) }
  have hthickS : IsWThickSequence_S13 S wstar := by
    intro j
    obtain ⟨R'', hR'', hsm, hck⟩ := hgood (j + M₀)
    have hbp : H.basepoint ∈ riemannianBallOf H.metric H.basepoint (4 * R'') := by
      change riemannianEDistOf H.metric H.basepoint H.basepoint < ENNReal.ofReal (4 * R'')
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by
        have := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right RT 1)) hR''; linarith)
    obtain ⟨r, hr, hcr, hv⟩ := hthick _ (hM₀ (j + M₀) (Nat.le_add_left M₀ j)) (q (j + M₀)) R''
      (le_trans (le_max_left _ _) hR'') hsm (fun k'' hk p hp => hck k'' hk p hp) H.basepoint hbp
    have T := thickTransport_O68 (postStage_eq_sliceStage_CX4 (s (j + M₀)))
      (postMetric F.observation (s (j + M₀)).time) (s (j + M₀)).metric
      (postMetric_regularSlice F.observation (s (j + M₀))) (s (j + M₀)).time⁻¹
      (inv_pos.mpr (s (j + M₀)).positive)
      (inv_pos.mpr (lt_of_lt_of_le hTT (hM₀ (j + M₀) (Nat.le_add_left M₀ j))))
      (q (j + M₀) H.basepoint) r
    refine ⟨r, hr, T.1.trans hcr, ?_⟩
    rw [show ballVolume (S.slices j).normalizedMetric (S.point j) r = _ from T.2]
    exact hv
  obtain ⟨σ', hσ', H', hconv⟩ := hcpt hw S hthickS
  obtain ⟨Φ, C, hcan⟩ := hconv
  refine ⟨fun m => σ' m + M₀, fun a b hab => Nat.add_lt_add_right (hσ' hab) M₀, H',
    S.subsequence σ' hσ', fun j => hthickS (σ' j), ⟨Φ, C, hcan⟩, ?_,
    fun m => sliceApprox_O32 (S.subsequence σ' hσ') H' Φ m, ?_,
    hconvS_O32 F H' (S.subsequence σ' hσ') Φ C hcan⟩
  · intro i R
    obtain ⟨M, hM⟩ := hesc i R
    refine ⟨M, fun j hj hij => ?_⟩
    rintro ⟨x, ⟨z, hz, rfl⟩, hx⟩
    have hle : M ≤ σ' j + M₀ := le_trans hj (le_trans (hσ'.id_le j) (Nat.le_add_right _ _))
    refine hM (σ' j + M₀) hle hij ⟨z, hz, ?_⟩
    exact eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq hx).trans (cast_heq _ _)))
  · intro m
    exact eq_of_heq ((cast_heq _ _).trans ((heq_of_eq (Φ.basepoint_map m)).trans (cast_heq _ _)))

end GC.LongTime.Ch12
