import FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface
import FailureOfSemipositiveMetricExtension.CaoFamilyAdapter
import FailureOfSemipositiveMetricExtension.CentralCurveNormalSimple
import FailureOfSemipositiveMetricExtension.CentralResidualMinimality

/-! Every actual line, section, reduced curve, pullback degree and tensor field
for the general negative-curve interface. No existence result is assumed here. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.NegativeCurveAdapter
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def line (a : ℤ) (b : Fin 4 → ℤ) : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.AnalyticLine (GlobalIncidence.Fiber 0) Index where
  core := core 0 a b
  analytic := core_isContMDiff 0 a b ω
  gain := gain 0 a b
  coordChange_eq _ _ _ _ := rfl

def asSection {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData 0 a b) : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.Section (line a b) where
  value := sectionValue s
  coefficient := s.coefficient
  represents i p hp := congrArg Prod.snd (sectionMap_localTriv s i p hp)
  analytic := s.analytic

def weight {a : ℤ} {b : Fin 4 → ℤ} (h : SingularHermitianWeight 0 a b) : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.Weight (line a b) where
  weight := h.weight
  compatible := h.compatible

theorem weight_psh {a : ℤ} {b : Fin 4 → ℤ} (h : SingularHermitianWeight 0 a b)
    (hh : HasPlurisubharmonicWeights h) : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.IsPsh CaoAdapter.centralAtlas (weight h) := by
  intro a i
  exact hh i a.1 a.2

def powerProduct : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.PowerProduct (line (-2) (fun _ => 1))
    (line (-2) centralADegree) (line (-2) ellDegree) 2 where
  base_B := rfl
  base_D := rfl
  identity i j p hp := (central_gain_square i j p hp).symm

def generators : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.Generators (line (-2) centralADegree) where
  count := 4
  sections k := asSection (liftedCentralCubics k)
  no_common_zero := liftedCentralCubics_basepoint_free

def divisor : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.RationalSimpleDivisor (line (-2) ellDegree) where
  equation := asSection ellSection
  curve := CurvePullback.analyticParam
  closedEmbedding := lineParam_isClosedEmbedding
  tangent_injective := lineParam_mfderiv_injective
  zero_range p := by
    constructor
    · rintro ⟨d,rfl⟩
      exact ellSection_lineParam_zero d
    · exact lineParam_surjective_zero p
  simple i p hp hz := by
    obtain ⟨d,rfl⟩ := hz
    exact CurveNormal.frameDerivative_surjective i d hp

theorem a_hasPullbackDegree : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.HasPullbackDegree (line (-2) centralADegree) divisor.curve 0 :=
  ⟨CurvePullback.aHomeomorph,CurvePullback.aHomeomorph_analytic.1,
    CurvePullback.aHomeomorph_analytic.2,CurvePullback.aFiberEquiv,CurvePullback.aHomeomorph_mk⟩

theorem ell_hasPullbackDegree : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.HasPullbackDegree (line (-2) ellDegree) divisor.curve (-2) :=
  ⟨CurvePullback.ellHomeomorph,CurvePullback.ellHomeomorph_analytic.1,
    CurvePullback.ellHomeomorph_analytic.2,CurvePullback.ellFiberEquiv,CurvePullback.ellHomeomorph_mk⟩

/-- An actual generic residual yields the prior exact residual data. This is a
conversion theorem, not an existence assumption or a literature axiom. -/
def halfDivisorResidual (h : SingularHermitianWeight 0 (-2) (fun _ => 1))
    (r : FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.Residual CaoAdapter.centralAtlas (B := line (-2) centralADegree) 2
      divisor.equation (weight h)) : HalfDivisorResidual h where
  remainder := ⟨r.remainder.weight,r.remainder.compatible⟩
  upperSemicontinuous := r.upperSemicontinuous
  square_identity i p hp := by
    have he := r.identity i p hp
    change scaleWeight 2 (h.weight i p) = _ at he
    have hd : scaleWeight 2 (h.weight i p) = h.weight i p + h.weight i p := by
      cases h.weight i p with
      | bot => simp
      | coe x => simp only [scaleWeight_coe,← WithBot.coe_add]; congr 1; ring
    rw [hd] at he
    exact he

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.NegativeCurveAdapter
