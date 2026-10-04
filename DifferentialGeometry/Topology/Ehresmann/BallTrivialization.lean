import DifferentialGeometry.Topology.Ehresmann.ProperSubmersion
import DifferentialGeometry.Topology.Ehresmann.LocalTriviality
import DifferentialGeometry.Topology.VectorField.OpenRestriction
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Proper submersions onto a planar disk are trivial over smaller disks (LC83 supplier)

Blueprint 207A, LC83 (`prop:collapse-two-stratum-local`, A:25167–25199) needs: a proper smooth
submersion `f : M → B(0, r) ⊂ ℝ²` is a trivial bundle over `B(0, R)` for every `R < r`.

* `compactSupportFlowDiffeomorph_eq_add_smul`: the flow of a compactly supported field `v` on a
  vector space that equals the constant `e` on an open convex set `S` is the translation by `t • e`
  along segments in `S`.
* `exists_trivialization_of_related_family_of_section`: a smooth family `D t` of diffeomorphisms
  covering a family `d t` of the base, with a smooth section `σ` of `t ↦ d t y` over an open
  `Q ∋ y`, trivializes `f` over `Q` (the tree's local-triviality argument with an explicit section).
* `exists_trivialization_over_planeBall_of_proper`: the global trivialization over `B(0, R)`,
  obtained from lifts of the two cut-off coordinate fields; the base flows are translations along
  the L-shaped path `0 → t₀ e₀ → t₀ e₀ + t₁ e₁`, which stays in `B(0, ‖t‖)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Analysis.ODE DifferentialGeometry.Topology.Manifold

section VectorSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem contMDiff_modelTangentSection_of_contDiff {v : F → F} (hv : ContDiff ℝ ∞ v) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent ∞
      (fun x : F => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, F) F)) := by
  intro x
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, ?_⟩
  refine hv.contMDiff.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards with y
  rw [trivializationAt_model_space_apply]

theorem compactSupportFlowDiffeomorph_eq_add_smul {v : F → F} (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport v) {S : Set F} (hS : IsOpen S) (hSc : Convex ℝ S) {e : F}
    (hvS : ∀ w ∈ S, v w = e) {w : F} {t : ℝ} (hw : w ∈ S) (hwt : w + t • e ∈ S) :
    compactSupportFlowDiffeomorph (I := 𝓘(ℝ, F)) v
      (contMDiff_modelTangentSection_of_contDiff hv) hc t w = w + t • e := by
  set T : Set ℝ := {s | w + s • e ∈ S} with hTdef
  have hTo : IsOpen T := hS.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hTc : T.OrdConnected := by
    have hconv : Convex ℝ T := by
      intro x hx y hy a b ha hb hab
      have := hSc hx hy ha hb hab
      change w + (a • x + b • y) • e ∈ S
      convert this using 1
      rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul, add_smul,
        smul_assoc, smul_assoc]
    exact hconv.ordConnected
  have h0 : (0 : ℝ) ∈ T := by simpa [hTdef] using hw
  have ht : t ∈ T := hwt
  obtain ⟨ε₀, hε₀, hb0⟩ := Metric.isOpen_iff.mp hTo 0 h0
  obtain ⟨ε₁, hε₁, hbt⟩ := Metric.isOpen_iff.mp hTo t ht
  set a := min 0 t - min ε₀ ε₁ / 2
  set b := max 0 t + min ε₀ ε₁ / 2
  have hmin : 0 < min ε₀ ε₁ := lt_min hε₀ hε₁
  have hsub : Ioo a b ⊆ T := by
    intro s hs
    have haT : min 0 t - min ε₀ ε₁ / 2 ∈ T := by
      rcases le_total 0 t with h | h
      · apply hb0; rw [mem_ball, Real.dist_eq, min_eq_left h]
        rw [abs_of_neg (by linarith)]; linarith [min_le_left ε₀ ε₁]
      · apply hbt; rw [mem_ball, Real.dist_eq, min_eq_right h]
        rw [abs_of_neg (by linarith)]; linarith [min_le_right ε₀ ε₁]
    have hbT : max 0 t + min ε₀ ε₁ / 2 ∈ T := by
      rcases le_total 0 t with h | h
      · apply hbt; rw [mem_ball, Real.dist_eq, max_eq_right h]
        rw [abs_of_pos (by linarith)]; linarith [min_le_right ε₀ ε₁]
      · apply hb0; rw [mem_ball, Real.dist_eq, max_eq_left h]
        rw [abs_of_pos (by linarith)]; linarith [min_le_left ε₀ ε₁]
    exact hTc.out haT hbT ⟨hs.1.le, hs.2.le⟩
  have hta : t ∈ Ioo a b := ⟨by simp only [a]; linarith [min_le_right (0:ℝ) t],
    by simp only [b]; linarith [le_max_right (0:ℝ) t]⟩
  have h0a : (0 : ℝ) ∈ Ioo a b := ⟨by simp only [a]; linarith [min_le_left (0:ℝ) t],
    by simp only [b]; linarith [le_max_left (0:ℝ) t]⟩
  let γ : ℝ → F := fun s => w + s • e
  have hγ : IsMIntegralCurveOn (I := 𝓘(ℝ, F)) γ (fun x : F => (v x : TangentSpace 𝓘(ℝ, F) x)) (Ioo a b) := by
    intro s hs
    have hd : HasDerivAt γ e s := by
      have h1 := ((hasDerivAt_id s).smul_const e).const_add w
      simp only [id, one_smul] at h1
      exact h1
    have hvs : v (γ s) = e := hvS _ (hsub hs)
    change HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ (Ioo a b) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ s)))
    rw [hvs]
    exact (hasMFDerivAt_iff_hasFDerivAt.mpr hd.hasFDerivAt).hasMFDerivWithinAt
  have hcurve := curveAt_integralCurve (I := 𝓘(ℝ, F)) (fun x : F => (v x : TangentSpace 𝓘(ℝ, F) x))
    (exists_globalIntegralCurve_of_compactSupport (I := 𝓘(ℝ, F)) v
      (contMDiff_modelTangentSection_of_contDiff hv) hc) w
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless h0a
    ((contMDiff_modelTangentSection_of_contDiff hv).of_le (by norm_num))
    (hcurve.isMIntegralCurveOn _) hγ (by
      have h0c := curveAt_zero (I := 𝓘(ℝ, F)) (fun x : F => (v x : TangentSpace 𝓘(ℝ, F) x))
        (exists_globalIntegralCurve_of_compactSupport (I := 𝓘(ℝ, F)) v
          (contMDiff_modelTangentSection_of_contDiff hv) hc) w
      exact h0c.trans (by simp [γ]))
  exact heq hta


end VectorSpace

section Section

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- A smooth family of diffeomorphisms `D t` of `M` covering a family `d t` of `N`, together with a
smooth section `σ : Q → P` of `t ↦ d t y` over an open `Q ∋ y`, trivializes `f` over `Q`. -/
theorem exists_trivialization_of_related_family_of_section
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : M → N) (hf : ContMDiff I J ∞ f) (hreg : ∀ x, Surjective (mfderiv I J f x)) (y : N)
    (D : P → M ≃ₘ⟮I, I⟯ M) (d : P → N ≃ₘ⟮J, J⟯ N)
    (hD : ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun p : P × M ↦ D p.1 p.2))
    (hDi : ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun p : P × M ↦ (D p.1).symm p.2))
    (hrel : ∀ t x, f (D t x) = d t (f x))
    (Q : TopologicalSpace.Opens N) (hy : y ∈ Q) (σ : Q → P) (hσ : ContMDiff J 𝓘(ℝ, P) ∞ σ)
    (hσy : σ ⟨y, hy⟩ = 0) (hσright : ∀ z : Q, d (σ z) y = z.1)
    (hD0 : D 0 = Diffeomorph.refl I M ∞) :
    let _ := regularFiberChartedSpace f y hf (fun x _ ↦ hreg x)
    let U : TopologicalSpace.Opens M := ⟨f ⁻¹' Q, Q.isOpen.preimage hf.continuous⟩
    ∃ Θ : Diffeomorph
        (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ).prod J) I
        ({x : M // f x = y} × Q) U ∞,
      (∀ p, f (Θ p).1 = p.2.1) ∧ (∀ x, (Θ (x, ⟨y, hy⟩)).1 = x.1) := by
  dsimp only
  let _ := regularFiberChartedSpace f y hf (fun x _ ↦ hreg x)
  let K := Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
  let U : TopologicalSpace.Opens M := ⟨f ⁻¹' Q, Q.isOpen.preimage hf.continuous⟩
  have hreturn : ∀ z : U, f ((D (σ ⟨f z.1, z.2⟩)).symm z.1) = y := by
    intro z
    apply (d (σ ⟨f z.1, z.2⟩)).injective
    change d (σ ⟨f z.1, z.2⟩) (f ((D (σ ⟨f z.1, z.2⟩)).symm z.1)) =
      d (σ ⟨f z.1, z.2⟩) y
    rw [← hrel, Diffeomorph.apply_symm_apply, hσright]
  let forward : {x : M // f x = y} × Q → U := fun p ↦
    ⟨D (σ p.2) p.1.1, by
      change f (D (σ p.2) p.1.1) ∈ Q
      rw [hrel, p.1.2, hσright]
      exact p.2.2⟩
  let inverse : U → {x : M // f x = y} × Q := fun z ↦
    (⟨(D (σ ⟨f z.1, z.2⟩)).symm z.1, hreturn z⟩, ⟨f z.1, z.2⟩)
  have hover : ∀ p, f (forward p).1 = p.2.1 := by
    intro p
    change f (D (σ p.2) p.1.1) = p.2.1
    rw [hrel, p.1.2, hσright]
  have hleft : ∀ p, inverse (forward p) = p := by
    intro p
    have hz : (⟨f (forward p).1, (forward p).2⟩ : Q) = p.2 := Subtype.ext (hover p)
    apply Prod.ext
    · apply Subtype.ext
      change (D (σ ⟨f (forward p).1, (forward p).2⟩)).symm (D (σ p.2) p.1.1) = p.1.1
      rw [hz, Diffeomorph.symm_apply_apply]
    · exact hz
  have hright : ∀ z, forward (inverse z) = z := by
    intro z
    apply Subtype.ext
    exact (D (σ ⟨f z.1, z.2⟩)).apply_symm_apply z.1
  have hforward : ContMDiff (𝓘(ℝ, K).prod J) I ∞ forward := by
    apply (ContMDiff.subtypeVal_comp_iff U forward).mp
    exact hD.comp ((hσ.comp contMDiff_snd).prodMk
      ((contMDiff_regularFiberInclusion f y hf (fun x _ ↦ hreg x)).comp contMDiff_fst))
  have hheight : ContMDiff I J ∞ (fun z : U ↦ (⟨f z.1, z.2⟩ : Q)) := by
    apply (ContMDiff.subtypeVal_comp_iff Q _).mp
    exact hf.comp contMDiff_subtype_val
  have hinverse : ContMDiff I (𝓘(ℝ, K).prod J) ∞ inverse := by
    apply ContMDiff.prodMk _ hheight
    apply (contMDiff_regularFiber_iff f y hf (fun x _ ↦ hreg x) _).mpr
    exact hDi.comp ((hσ.comp hheight).prodMk contMDiff_subtype_val)
  let Θ : Diffeomorph (𝓘(ℝ, K).prod J) I ({x : M // f x = y} × Q) U ∞ :=
    { toEquiv := ⟨forward, inverse, hleft, hright⟩
      contMDiff_toFun := hforward
      contMDiff_invFun := hinverse }
  refine ⟨Θ, hover, ?_⟩
  intro x
  change D (σ ⟨y, hy⟩) x.1 = x.1
  rw [hσy, hD0]
  rfl

end Section

section Ball

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The open Euclidean ball `B(0, r)` of `ℝ²` as an open set. -/
def planeBallOpens (r : ℝ) : TopologicalSpace.Opens ℝ² := ⟨ball 0 r, isOpen_ball⟩

theorem mem_planeBallOpens_iff {r : ℝ} {w : ℝ²} : w ∈ planeBallOpens r ↔ ‖w‖ < r := by
  change w ∈ ball (0 : ℝ²) r ↔ _
  rw [mem_ball, dist_zero_right]

theorem zero_mem_planeBallOpens {r : ℝ} (hr : 0 < r) : (0 : ℝ²) ∈ planeBallOpens r :=
  mem_planeBallOpens_iff.mpr (by simpa using hr)

/-- The ball `B(0, R)` inside the manifold `B(0, r)`. -/
def planeBallInner (r R : ℝ) : TopologicalSpace.Opens (planeBallOpens r) :=
  ⟨Subtype.val ⁻¹' ball 0 R, isOpen_ball.preimage continuous_subtype_val⟩

theorem mem_planeBallInner_iff {r R : ℝ} {z : planeBallOpens r} :
    z ∈ planeBallInner r R ↔ ‖(z : ℝ²)‖ < R := by
  change (z : ℝ²) ∈ ball (0 : ℝ²) R ↔ _
  rw [mem_ball, dist_zero_right]

private theorem norm_smul_single_le (c : ℝ) (i : Fin 2) (w : ℝ²) (hc : c = w i) :
    ‖c • EuclideanSpace.single i (1 : ℝ)‖ ≤ ‖w‖ := by
  have h1 : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  rw [norm_smul, h1, mul_one, hc]
  exact PiLp.norm_apply_le w i

private theorem eq_sum_single (w : ℝ²) :
    w = w 0 • EuclideanSpace.single 0 (1 : ℝ) + w 1 • EuclideanSpace.single 1 (1 : ℝ) := by
  ext j
  fin_cases j <;> simp

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

/-- A proper smooth submersion onto the open disk `B(0, r) ⊂ ℝ²` is trivial over every smaller
disk `B(0, R)`: the inverse image of `B(0, R)` is diffeomorphic to (fibre over `0`) × `B(0, R)`,
over the identity of `B(0, R)` and restricting to the identity on the zero fibre. -/
theorem exists_trivialization_over_planeBall_of_proper {r : ℝ}
    (f : M → planeBallOpens r) (hf : ContMDiff I 𝓘(ℝ, ℝ²) ∞ f) (hp : IsProperMap f)
    (hreg : ∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) {R : ℝ} (hR : 0 < R) (hRr : R < r) :
    let y₀ : planeBallOpens r := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
    let _ := regularFiberChartedSpace f y₀ hf (fun x _ ↦ hreg x)
    let U : TopologicalSpace.Opens M :=
      ⟨f ⁻¹' planeBallInner r R, (planeBallInner r R).isOpen.preimage hf.continuous⟩
    ∃ (hy : y₀ ∈ planeBallInner r R) (Θ : Diffeomorph
        (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
        ({x : M // f x = y₀} × planeBallInner r R) U ∞),
      (∀ p, f (Θ p).1 = p.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1) := by
  intro y₀
  dsimp only
  have hy : y₀ ∈ planeBallInner r R := mem_planeBallInner_iff.mpr (by simpa [y₀] using hR)
  let N := planeBallOpens r
  let Q := planeBallInner r R
  let b : ContDiffBump (0 : ℝ²) :=
    { rIn := (2 * R + r) / 3, rOut := (R + 2 * r) / 3,
      rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  let e : Fin 2 → ℝ² := fun i => EuclideanSpace.single i (1 : ℝ)
  let V : Fin 2 → ℝ² → ℝ² := fun i w => b w • e i
  have hV : ∀ i, ContDiff ℝ ∞ (V i) := fun i => b.contDiff.smul contDiff_const
  have hVc : ∀ i, HasCompactSupport (V i) := fun i => b.hasCompactSupport.smul_right
  have hVS : ∀ i, ∀ w ∈ ball (0 : ℝ²) ((2 * R + r) / 3), V i w = e i := by
    intro i w hw
    simp only [V, b.one_of_mem_closedBall (ball_subset_closedBall hw), one_smul]
  let Z : Fin 2 → (z : N) → TangentSpace 𝓘(ℝ, ℝ²) z := fun i z => V i z.1
  have hZ : ∀ i, ContMDiff 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ²).tangent ∞
      (fun z : N => (⟨z, Z i z⟩ : TangentBundle 𝓘(ℝ, ℝ²) N)) := fun i =>
    DifferentialGeometry.VectorField.contMDiff_tangentSection_restrict_opens N
      (contMDiff_modelTangentSection_of_contDiff (hV i)).contMDiffOn
  have hZc : ∀ i, IsCompact (tsupport (Z i)) := by
    intro i
    have hsub : tsupport (V i) ⊆ (N : Set ℝ²) := by
      intro w hw
      have hw' : w ∈ tsupport b := tsupport_smul_subset_left _ _ hw
      rw [b.tsupport_eq, mem_closedBall, dist_zero_right] at hw'
      change ‖w‖ ≤ (R + 2 * r) / 3 at hw'
      exact mem_planeBallOpens_iff.mpr (by linarith)
    have hK : IsCompact (Subtype.val ⁻¹' tsupport (V i) : Set N) := by
      rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
      have heq : tsupport (V i) ∩ {x | x ∈ N} = tsupport (V i) :=
        inter_eq_left.mpr (fun w hw => hsub hw)
      rw [heq]
      exact hVc i
    exact hK.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset_preimage (V i) continuous_subtype_val)
  have hlift := fun i => exists_compactlySupported_relatedFlow_of_surjective f hp hf hreg
    (Z i) (hZ i) (hZc i)
  choose X hXc hrelX hsuppX hflow using hlift
  let d : Fin 2 → ℝ → N ≃ₘ⟮𝓘(ℝ, ℝ²), 𝓘(ℝ, ℝ²)⟯ N := fun i =>
    compactSupportFlowDiffeomorph (Z i) (hZ i) (hZc i)
  let D : Fin 2 → ℝ → M ≃ₘ⟮I, I⟯ M := fun i =>
    compactSupportFlowDiffeomorph (X i) (X i).contMDiff (hXc i)
  have hbase : ∀ i t (z : N), (d i t z : ℝ²) =
      compactSupportFlowDiffeomorph (I := 𝓘(ℝ, ℝ²)) (V i)
        (contMDiff_modelTangentSection_of_contDiff (hV i)) (hVc i) t z.1 := by
    intro i t z
    exact compactSupportFlowDiffeomorph_map_of_mfderiv_eq (Subtype.val : N → ℝ²)
      contMDiff_subtype_val (Z i) (hZ i) (hZc i) (V i)
      (contMDiff_modelTangentSection_of_contDiff (hV i)) (hVc i)
      (fun z => DifferentialGeometry.mfderiv_subtype_val_apply (I := 𝓘(ℝ, ℝ²)) N z (Z i z)) t z
  have htrans : ∀ i t (z : N), ‖(z : ℝ²)‖ < (2 * R + r) / 3 →
      ‖(z : ℝ²) + t • e i‖ < (2 * R + r) / 3 → (d i t z : ℝ²) = z + t • e i := by
    intro i t z hz hzt
    rw [hbase]
    exact compactSupportFlowDiffeomorph_eq_add_smul (hV i) (hVc i) isOpen_ball (convex_ball _ _)
      (hVS i) (by rwa [mem_ball, dist_zero_right]) (by rwa [mem_ball, dist_zero_right])
  let l : List (Fin 2) := [0, 1]
  let Dl : (Fin 2 → ℝ) → M ≃ₘ⟮I, I⟯ M := diffeomorphList D l
  let dl : (Fin 2 → ℝ) → N ≃ₘ⟮𝓘(ℝ, ℝ²), 𝓘(ℝ, ℝ²)⟯ N := diffeomorphList d l
  have hDj : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ D i p.1 p.2) := fun i ↦
    contMDiff_globalFlow_joint_of_compactSupport (X i) (X i).contMDiff (hXc i)
  have hDji : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ (D i p.1).symm p.2) :=
    fun i ↦ (hDj i).comp (contMDiff_fst.neg.prodMk contMDiff_snd)
  have hrel : ∀ t x, f (Dl t x) = dl t (f x) := by
    intro t x
    change f (D 1 (t 1) (D 0 (t 0) x)) = d 1 (t 1) (d 0 (t 0) (f x))
    rw [hflow, hflow]
  let σ : Q → (Fin 2 → ℝ) := fun z => EuclideanSpace.equiv (Fin 2) ℝ (z : N)
  have hσ : ContMDiff 𝓘(ℝ, ℝ²) 𝓘(ℝ, Fin 2 → ℝ) ∞ σ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).contDiff.contMDiff.comp
      (contMDiff_subtype_val.comp contMDiff_subtype_val)
  have hσy : σ ⟨y₀, hy⟩ = 0 := by
    change EuclideanSpace.equiv (Fin 2) ℝ 0 = 0
    exact map_zero _
  have hσright : ∀ z : Q, dl (σ z) y₀ = z.1 := by
    intro z
    have hzR : ‖((z : N) : ℝ²)‖ < R := mem_planeBallInner_iff.mp z.2
    set w : ℝ² := ((z : N) : ℝ²) with hw
    have hw0 : (σ z) 0 = w 0 := rfl
    have hw1 : (σ z) 1 = w 1 := rfl
    have hR3 : R < (2 * R + r) / 3 := by linarith
    have h0 : ‖w 0 • e 0‖ ≤ ‖w‖ := norm_smul_single_le _ 0 w rfl
    have hy0 : ((y₀ : N) : ℝ²) = 0 := rfl
    have hA : ‖((y₀ : N) : ℝ²)‖ < (2 * R + r) / 3 := by
      rw [hy0, norm_zero]
      linarith
    have hB : ‖((y₀ : N) : ℝ²) + (σ z) 0 • e 0‖ < (2 * R + r) / 3 := by
      rw [hy0, zero_add, hw0]
      exact h0.trans_lt (hzR.trans hR3)
    have hstep0 : (d 0 ((σ z) 0) y₀ : ℝ²) = w 0 • e 0 := by
      rw [htrans 0 _ y₀ hA hB, hy0, zero_add, hw0]
    have hC : ‖(d 0 ((σ z) 0) y₀ : ℝ²)‖ < (2 * R + r) / 3 := by
      rw [hstep0]
      exact h0.trans_lt (hzR.trans hR3)
    have hD : ‖(d 0 ((σ z) 0) y₀ : ℝ²) + (σ z) 1 • e 1‖ < (2 * R + r) / 3 := by
      rw [hstep0, hw1, ← eq_sum_single]
      exact hzR.trans hR3
    have hstep1 : (d 1 ((σ z) 1) (d 0 ((σ z) 0) y₀) : ℝ²) = w := by
      rw [htrans 1 _ _ hC hD, hstep0, hw1]
      exact (eq_sum_single w).symm
    exact Subtype.ext hstep1
  have hD0 : Dl 0 = Diffeomorph.refl I M ∞ :=
    diffeomorphList_zero D (fun i => compactSupportFlowDiffeomorph_zero (X i) (X i).contMDiff
      (hXc i)) l
  exact ⟨hy, exists_trivialization_of_related_family_of_section f hf hreg y₀ Dl dl
    (contMDiff_diffeomorphList D hDj l) (contMDiff_diffeomorphList_symm D hDji l) hrel Q hy σ hσ
    hσy hσright hD0⟩

end Ball

end DifferentialGeometry.Topology.Ehresmann
