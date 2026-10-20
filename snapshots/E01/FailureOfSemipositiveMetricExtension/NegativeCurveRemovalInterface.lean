import FailureOfSemipositiveMetricExtension.CaoExtensionInterface
import FailureOfSemipositiveMetricExtension.CentralCurveDegreeBundles
import FailureOfSemipositiveMetricExtension.PlurisubharmonicScaling

/-! Pure definitions for review of a GENERIC negative-curve psh-removal
corollary. This file contains no axiom and proves no existence statement.
The proposed statement is not imported by the frozen stage-7 root. -/
namespace FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface
noncomputable section
open Set Bundle IsManifold TopologicalSpace Topology
open scoped Manifold ContDiff

abbrev Coord := ℂ × ℂ
variable (M : Type) [TopologicalSpace M] [ChartedSpace Coord M]

/-- Actual holomorphic line bundle with the coefficient convention c_j=g_ij c_i. -/
structure AnalyticLine (J : Type) where
  core : VectorBundleCore ℂ M ℂ J
  analytic : core.IsContMDiff 𝓘(ℂ,Coord) ω
  gain : J → J → M → ℂ
  coordChange_eq : ∀ i j p z, core.coordChange i j p z = gain i j p * z

variable {M} {J A : Type}

/-- Sections take values in the actual line fibres; their coefficients are not
uninterpreted functions standing in for an unspecified geometric section. -/
structure Section (L : AnalyticLine M J) where
  value : ∀ p : M, L.core.Fiber p
  coefficient : J → M → ℂ
  represents : ∀ i p, p ∈ L.core.baseSet i →
    (L.core.localTriv i ⟨p,value p⟩).2 = coefficient i p
  analytic : ∀ i, ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ) ω (coefficient i) (L.core.baseSet i)

structure Weight (L : AnalyticLine M J) where
  weight : J → M → WithBot ℝ
  compatible : ∀ i j p, p ∈ L.core.baseSet i ∩ L.core.baseSet j →
    weight j p = weight i p + ((Real.log (Complex.normSq (L.gain i j p)) : ℝ) : WithBot ℝ)

def IsPsh (atlas : CaoExtensionInterface.AnalyticAtlas Coord M A)
    {L : AnalyticLine M J} (h : Weight L) : Prop :=
  ∀ a i, PlurisubharmonicOn (fun q => h.weight i ((atlas.chart a).symm q))
    ((atlas.chart a).target ∩ (atlas.chart a).symm ⁻¹' L.core.baseSet i)

/-- Concrete finite projective maps and actual joint complex tangent injection;
its Kähler consequence would be a disclosed standard literature translation. -/
structure ProjectiveImmersion where
  planeCount : ℕ
  lineCount : ℕ
  plane : Fin planeCount → M → ProjectivePlane.Point
  line : Fin lineCount → M → ProjectiveLine.Point
  plane_analytic : ∀ i, ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) ω (plane i)
  line_analytic : ∀ i, ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ) ω (line i)
  joint_tangent_injective : ∀ p, Function.Injective
    (fun v : TangentSpace 𝓘(ℂ,Coord) p =>
      ((fun i => mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) (plane i) p v),
       (fun i => mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ) (line i) p v)))

/-- Genuine standard pullback analytically isomorphic to the standard actual
P¹ degree-k bundle, with base-preserving complex-linear fibre maps. -/
def HasPullbackDegree (L : AnalyticLine M J)
    (j : C^ω⟮𝓘(ℂ),ProjectiveLine.Point;𝓘(ℂ,Coord),M⟯) (k : ℤ) : Prop :=
  letI := L.analytic
  ∃ e : TotalSpace ℂ (j *ᵖ L.core.Fiber) ≃ₜ (ProjectiveLineBundle.core k).TotalSpace,
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω e ∧
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω e.symm ∧
    ∃ E : ∀ p : ProjectiveLine.Point, (j *ᵖ L.core.Fiber) p ≃L[ℂ]
      (ProjectiveLineBundle.core k).Fiber p,
      ∀ p v, e ⟨p,v⟩ = ⟨p,E p v⟩

/-- The actual zero divisor is a single smoothly embedded rational curve.
Surjectivity of the actual derivative of each local equation fixes multiplicity
one. No abstract predicate named smooth divisor is assumed. -/
structure RationalSimpleDivisor (D : AnalyticLine M J) where
  equation : Section D
  curve : C^ω⟮𝓘(ℂ),ProjectiveLine.Point;𝓘(ℂ,Coord),M⟯
  closedEmbedding : IsClosedEmbedding curve
  tangent_injective : ∀ p, Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ,Coord) curve p)
  zero_range : ∀ p, p ∈ Set.range curve ↔ equation.value p = 0
  simple : ∀ i p, p ∈ D.core.baseSet i → p ∈ Set.range curve →
    Function.Surjective (mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ) (equation.coefficient i) p)

/-- A genuine globally generated analytic bundle, via actual global sections. -/
structure Generators (L : AnalyticLine M J) where
  count : ℕ
  sections : Fin count → Section L
  no_common_zero : ∀ p, ∃ k, (sections k).value p ≠ 0

/-- Exact Cech tensor identity on the same actual open trivializations. The
standard tensor/Picard/Chern translation would be separately disclosed. -/
structure PowerProduct (L B D : AnalyticLine M J) (m : ℕ) where
  base_B : B.core.baseSet = L.core.baseSet
  base_D : D.core.baseSet = L.core.baseSet
  identity : ∀ i j p, p ∈ L.core.baseSet i ∩ L.core.baseSet j →
    L.gain i j p ^ m = B.gain i j p * D.gain i j p

def divisorWeight {D : AnalyticLine M J} (s : Section D) (i : J) (p : M) : WithBot ℝ :=
  if s.coefficient i p = 0 then ⊥ else ((Real.log (Complex.normSq (s.coefficient i p)) : ℝ) : WithBot ℝ)

/-- The output is an actual compatible weight of B, upper semicontinuous in
actual frames, with an exact extended-value identity, including the divisor. -/
structure Residual (atlas : CaoExtensionInterface.AnalyticAtlas Coord M A)
    {L B D : AnalyticLine M J} (m : ℕ)
    (s : Section D) (h : Weight L) where
  remainder : Weight B
  psh : IsPsh atlas remainder
  upperSemicontinuous : ∀ i, UpperSemicontinuousOn (remainder.weight i) (B.core.baseSet i)
  identity : ∀ i p, p ∈ L.core.baseSet i →
    scaleWeight (m : ℝ) (h.weight i p) = remainder.weight i p + divisorWeight s i p

/-- REVIEW CANDIDATE ONLY. The general negative-curve corollary has arbitrary
surface, bundles, exponent m>0 and negative degree -n. No particular h0, sigma,
four-point family, or minimality/nonextension conclusion is a hypothesis. -/
def RemovalStatement [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold 𝓘(ℂ,Coord) ω M]
    (atlas : CaoExtensionInterface.AnalyticAtlas Coord M A)
    (L B D : AnalyticLine M J) : Prop :=
  ∀ (_immersion : ProjectiveImmersion (M := M)) (m n : ℕ), 0 < m → 0 < n →
    PowerProduct L B D m → Generators B →
    ∀ divisor : RationalSimpleDivisor D,
      HasPullbackDegree B divisor.curve 0 →
      HasPullbackDegree D divisor.curve (-(n : ℤ)) →
      ∀ h : Weight L, IsPsh atlas h → Nonempty (Residual atlas (B := B) m divisor.equation h)

end
end FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface
