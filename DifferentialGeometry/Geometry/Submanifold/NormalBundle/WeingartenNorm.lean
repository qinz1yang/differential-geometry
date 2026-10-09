import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Geometry.Connection.SourceCovariantPartial
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Operator.OrthonormalTrace
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.OpenImmersion

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set DifferentialGeometry
open scoped ContDiff Manifold Topology BigOperators

namespace DifferentialGeometry.Geometry

open Riemannian Operator Curvature
open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem inner_sourceDerivative_normal
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : A → M} {s : Set A} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ U s)
    {W : ∀ q, TangentSpace 𝓘(ℝ, E) (U q)}
    (hW : ContMDiffOn 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (W q)) s)
    (hnormal : ∀ q ∈ s, ∀ a : A,
      g.inner (U q) (W q) (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U q a) = 0)
    {z : A} (hz : z ∈ s) (v w : A) :
    g.inner (U z) (sourceSectionCovariantDerivative g U W z v)
      (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U z w) =
        -g.inner (U z) (W z) (sourceCovariantPartial g U z v w) := by
  let B (q : A) : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U q)
  let D (q : A) : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U q
  let W₀ : A → E := W
  let p : A → ℝ := fun q => B q (W₀ q) (D q w)
  let DW : E := sourceSectionCovariantDerivative g U W z v
  let C : E := sourceCovariantPartial g U z v w
  have heq : p =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hs.mem_nhds hz] with q hq
    exact hnormal q hq w
  have hd : fderiv ℝ p z = 0 := heq.fderiv_eq.trans (fderiv_const_apply (0 : ℝ))
  have hpair : fderiv ℝ p z v = B z DW (D z w) + B z (W₀ z) C :=
    fderiv_sourceSectionPairing g hs hU hW
      (contMDiffOn_source_partial hs hU (by simp) w) hz v
  rw [hd, zero_apply] at hpair
  change B z DW (D z w) = -B z (W₀ z) C
  linarith

/-- The covariant energy of an actual scalar normal variation of a hypersurface.
The source metric is the induced metric, and the second fundamental form is
that of the same immersion. Codimension one removes any normal-connection term. -/
theorem normalVariation_covariantDerivative_norm_sq
    {m : ℕ} (N : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hdim : Module.finrank ℝ E = m + 1)
    (U : EuclideanSpace ℝ (Fin m) → M)
    (hU : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, E) ∞
      (fun q : N => U q))
    (hinj : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, E) (fun p : N => U p) q))
    (ν : ∀ q, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun q => TotalSpace.mk' E (U q) (ν q)) N)
    (hunit : ∀ q ∈ N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ q ∈ N, ∀ a : EuclideanSpace ℝ (Fin m),
      g.inner (U q) (ν q)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, E) U q a) = 0)
    (φ : EuclideanSpace ℝ (Fin m) → ℝ) (hφ : ContDiffOn ℝ ∞ φ N)
    (z : N) :
    let gN := g.pullback (fun q : N => U q) hU hinj
    ∀ (b : Module.Basis (Fin m) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) z))
      (_hb : ∀ i j, gN.inner z (b i) (b j) = if i = j then 1 else 0),
    let II := secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
    let W := fun q => φ q • ν q
    (∑ i, g.inner (U z)
      (sourceSectionCovariantDerivative g U W z (b i))
      (sourceSectionCovariantDerivative g U W z (b i))) =
      gN.inner z (gradFun gN (fun q : N => φ q) z) (gradFun gN (fun q : N => φ q) z) +
        φ z ^ 2 * ∑ i, ∑ j, g.inner (U z) (II (b i) (b j)) (II (b i) (b j)) := by
  dsimp only
  intro b hb
  classical
  let A := EuclideanSpace ℝ (Fin m)
  let gN := g.pullback (fun q : N => U q) hU hinj
  let Q : A →L[ℝ] A →L[ℝ] E :=
    secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  let B (q : A) : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U q)
  let P : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U z
  let P₀ : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun q : N => U q) z
  let b₀ : Module.Basis (Fin m) ℝ A := b
  let n : A → E := ν
  let W (q : A) : TangentSpace 𝓘(ℝ, E) (U q) := φ q • ν q
  let W₀ : A → E := W
  let DW (a : A) : E := sourceSectionCovariantDerivative g U W z a
  let Dν (a : A) : E := sourceSectionCovariantDerivative g U ν z a
  let C (a c : A) : E := sourceCovariantPartial g U z a c
  have hP : P₀ = P := DifferentialGeometry.mfderiv_restrict_open U N z
  have hsymm (v w : E) : B z v w = B z w v := g.symm (U z) v w
  have hn (q : A) (hq : q ∈ N) : B q (n q) (n q) = 1 := hunit q hq
  have hUon : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ U N := by
    intro q hq
    exact (contMDiffAt_subtype_iff.mp (hU.contMDiffAt (x := ⟨q, hq⟩))).contMDiffWithinAt
  have hW : ContMDiffOn 𝓘(ℝ, A) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (W q)) N := hφ.contMDiffOn.smul_bundle hν
  have hWnormal (q : A) (hq : q ∈ N) (a : A) :
      g.inner (U q) (W q) (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U q a) = 0 := by
    let D : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) U q
    have hh : B q (n q) (D a) = 0 := hnormal q hq a
    change B q (φ q • n q) (D a) = 0
    rw [map_smul, smul_apply, smul_eq_mul, hh, mul_zero]
  have hWP (a : A) : B z (W₀ z) (P a) = 0 := hWnormal z z.property a
  have hmetric (q : N) (a c : TangentSpace 𝓘(ℝ, A) q) :
      g.inner (U q) (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun p : N => U p) q a)
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (fun p : N => U p) q c) = gN.inner q a c := rfl
  have hIIpair (a c : A) : B z (W₀ z) (Q a c) = B z (W₀ z) (C a c) := by
    let correction : A := (metricCov gN)
      (fun q : N => (c : TangentSpace 𝓘(ℝ, A) q)) z a
    have heq : Q a c = C a c - P correction :=
      (immersionSecondFundamental_eq_secondFundamentalFormAmbientAt_of_contMDiffOn
        N U hUon g gN z a c).symm
    rw [heq, map_sub, hWP, sub_zero]
  have hWpair (a c : A) : B z (DW a) (P c) = -(φ z * B z (n z) (Q a c)) := by
    have hd : B z (DW a) (P c) = -B z (W₀ z) (C a c) :=
      inner_sourceDerivative_normal g N.isOpen hUon hW hWnormal z.property a c
    rw [← hIIpair] at hd
    change B z (DW a) (P c) = -B z (φ z • n z) (Q a c) at hd
    simpa only [map_smul, smul_apply, smul_eq_mul] using hd
  have hνself (a : A) : B z (Dν a) (n z) = 0 := by
    let p : A → ℝ := fun q => B q (n q) (n q)
    have heq : p =ᶠ[𝓝 (z : A)] fun _ => (1 : ℝ) := by
      filter_upwards [N.isOpen.mem_nhds z.property] with q hq
      exact hn q hq
    have hd : fderiv ℝ p z = 0 := heq.fderiv_eq.trans (fderiv_const_apply (1 : ℝ))
    have hpair : fderiv ℝ p z a = B z (Dν a) (n z) + B z (n z) (Dν a) :=
      fderiv_sourceSectionPairing g N.isOpen hUon hν hν z.property a
    rw [hd, zero_apply, hsymm (n z)] at hpair
    linarith
  have hWν (a : A) : B z (DW a) (n z) = fderiv ℝ φ z a := by
    let p : A → ℝ := fun q => B q (W₀ q) (n q)
    have heq : p =ᶠ[𝓝 (z : A)] φ := by
      filter_upwards [N.isOpen.mem_nhds z.property] with q hq
      change B q (φ q • n q) (n q) = φ q
      rw [map_smul, smul_apply, smul_eq_mul, hn q hq, mul_one]
    have hd : fderiv ℝ p z a = fderiv ℝ φ z a :=
      congrArg (fun L : A →L[ℝ] ℝ => L a) heq.fderiv_eq
    have hpair : fderiv ℝ p z a = B z (DW a) (n z) + B z (W₀ z) (Dν a) :=
      fderiv_sourceSectionPairing g N.isOpen hUon hW hν z.property a
    have hzν : B z (W₀ z) (Dν a) = 0 := by
      change B z (φ z • n z) (Dν a) = 0
      rw [map_smul, smul_apply, smul_eq_mul, hsymm (n z), hνself, mul_zero]
    rw [hzν, add_zero] at hpair
    exact hpair.symm.trans hd
  let frame : Option (Fin m) → E := fun i => i.elim (n z) (fun j => P (b₀ j))
  have hframe : ∀ i j, B z (frame i) (frame j) = if i = j then 1 else 0 := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none =>
        change B z (n z) (n z) = 1
        exact hn z z.property
      | some j =>
        change B z (n z) (P (b₀ j)) = 0
        exact hnormal z z.property (b₀ j)
    | some i =>
      cases j with
      | none =>
        have hh : B z (n z) (P (b₀ i)) = 0 := hnormal z z.property (b₀ i)
        change B z (P (b₀ i)) (n z) = 0
        exact (hsymm _ _).trans hh
      | some j =>
        have hh : B z (P₀ (b₀ i)) (P₀ (b₀ j)) = if i = j then 1 else 0 := hb i j
        rw [hP] at hh
        simpa only [frame, Option.elim_some, Option.some.injEq] using hh
  have hcard : Fintype.card (Option (Fin m)) =
      Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) (U z)) := by
    rw [Fintype.card_option, Fintype.card_fin]
    exact hdim.symm
  have hnorm (V : E) : B z V V = (B z (n z) V) ^ 2 +
      ∑ j, (B z (P (b₀ j)) V) ^ 2 := by
    have hh : B z V V = ∑ i, (B z (frame i) V) ^ 2 :=
      inner_self_eq_sum_sq g (U z) hcard frame hframe V
    simpa only [Fintype.sum_option, frame, Option.elim_none, Option.elim_some] using hh
  have hIInormal (a c d : A) : B z (Q a c) (P d) = 0 := by
    have hh : B z (Q a c) (P₀ d) = 0 :=
      secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map hU hmetric z a c d
    rwa [hP] at hh
  have hIInorm (a c : A) : B z (Q a c) (Q a c) = (B z (n z) (Q a c)) ^ 2 := by
    rw [hnorm]
    simp only [hsymm (P _), hIInormal, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, add_zero]
  have hpoint (a : A) : B z (DW a) (DW a) = (fderiv ℝ φ z a) ^ 2 +
      φ z ^ 2 * ∑ j, B z (Q a (b₀ j)) (Q a (b₀ j)) := by
    rw [hnorm, hsymm (n z), hWν]
    simp_rw [hsymm (P _), hWpair, neg_sq, mul_pow, hIInorm]
    rw [Finset.mul_sum]
  let Dφ : A →L[ℝ] ℝ := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℝ) (fun q : N => φ q) z
  have hDφ : Dφ = fderiv ℝ φ z :=
    (DifferentialGeometry.mfderiv_restrict_open φ N z).trans (mfderiv_eq_fderiv (f := φ) (x := (z : A)))
  have hgrad : gN.inner z (gradFun gN (fun q : N => φ q) z)
      (gradFun gN (fun q : N => φ q) z) = ∑ i, (Dφ (b₀ i)) ^ 2 :=
    inner_gradFun_self_eq_sum_sq gN (fun q : N => φ q) z b hb
  rw [hDφ] at hgrad
  change (∑ i, B z (DW (b₀ i)) (DW (b₀ i))) =
    gN.inner z (gradFun gN (fun q : N => φ q) z) (gradFun gN (fun q : N => φ q) z) +
      φ z ^ 2 * ∑ i, ∑ j, B z (Q (b₀ i) (b₀ j)) (Q (b₀ i) (b₀ j))
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hgrad]

end DifferentialGeometry.Geometry
