import FailureOfSemipositiveMetricExtension.CentralAuxiliarySections

/-! The nonzero actual analytic section σ=ℓ²Q in ambient multidegree
(-7;3,3,3,3), and the exact identity recovering z²xy(x-y) before division.
Identification of this line bundle with K+4L is a separate geometric bridge. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

/-- A genuine central-fibre point over [1:2:1], used to verify nonvanishing. -/
def auxiliaryWitness : Fiber 0 :=
  ⟨(FailureOfSemipositiveMetricExtension.ProjectivePlane.param 0 (2,1),
    fun r => chosenDirection (FailureOfSemipositiveMetricExtension.ProjectivePlane.param 0 (2,1)) r 0),
    fun r => chosenDirection_incidence _ r 0⟩

def auxiliaryWitnessFrame : Index :=
  (0,fun r => (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core 0).indexAt (auxiliaryWitness.val.2 r))

theorem auxiliaryWitness_mem_frame : auxiliaryWitness ∈ baseSet 0 auxiliaryWitnessFrame := by
  constructor
  · exact FailureOfSemipositiveMetricExtension.ProjectivePlane.param_mem_chartSet 0 (2,1)
  · intro r
    exact (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core 0).mem_baseSet_at _

theorem ellNumerator_witness : ellNumerator.coefficient auxiliaryWitnessFrame auxiliaryWitness = 1 := by
  change (FailureOfSemipositiveMetricExtension.ProjectivePlane.vector 0
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates 0 (FailureOfSemipositiveMetricExtension.ProjectivePlane.param 0 (2,1)))) 2 = 1
  rw [FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates_param]
  rfl

theorem qNumerator_witness : qNumerator.coefficient auxiliaryWitnessFrame auxiliaryWitness = -2 := by
  change (FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators 3).value
    (0,FailureOfSemipositiveMetricExtension.ProjectivePlane.vector 0
      (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates 0 (FailureOfSemipositiveMetricExtension.ProjectivePlane.param 0 (2,1)))) = -2
  rw [FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates_param]
  norm_num [FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators,FailureOfSemipositiveMetricExtension.ProjectivePlane.vector,
    FailureOfSemipositiveMetricExtension.Cubics.g₄,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]

theorem ellSection_witness_ne_zero : sectionValue ellSection auxiliaryWitness ≠ 0 := by
  intro hz
  have hc := (sectionValue_zero_iff ellSection auxiliaryWitnessFrame auxiliaryWitness
    auxiliaryWitness_mem_frame).mp hz
  have h := ellDivisionData.quotientSection_division auxiliaryWitnessFrame auxiliaryWitness
    auxiliaryWitness_mem_frame
  change ellSection.coefficient _ _ * _ = ellNumerator.coefficient _ _ at h
  rw [hc,zero_mul,ellNumerator_witness] at h
  exact zero_ne_one h

theorem qSection_witness_ne_zero : sectionValue qSection auxiliaryWitness ≠ 0 := by
  intro hz
  have hc := (sectionValue_zero_iff qSection auxiliaryWitnessFrame auxiliaryWitness
    auxiliaryWitness_mem_frame).mp hz
  have h := qDivisionData.quotientSection_division auxiliaryWitnessFrame auxiliaryWitness
    auxiliaryWitness_mem_frame
  change qSection.coefficient _ _ * _ = qNumerator.coefficient _ _ at h
  rw [hc,zero_mul,qNumerator_witness] at h
  norm_num at h

def sigmaSection : SectionData 0 (-7) (fun _ => 3) where
  coefficient := (multiplySections (multiplySections ellSection ellSection) qSection).coefficient
  analytic := (multiplySections (multiplySections ellSection ellSection) qSection).analytic
  compatible i j p hp := by
    have h := (multiplySections (multiplySections ellSection ellSection) qSection).compatible i j p hp
    have hb : (fun r => (ellDegree r+ellDegree r)+qDegree r) = (fun _ : Fin 4 => (3 : ℤ)) := by
      funext r
      fin_cases r <;> decide
    change gain 0 (-7) _ i j p * _ = _ at h
    conv at h => lhs; arg 1; rw [hb]
    exact h

theorem sigmaSection_coefficient (i : Index) (p : Fiber 0) :
    sigmaSection.coefficient i p = (ellSection.coefficient i p)^2 * qSection.coefficient i p := by
  change (ellSection.coefficient i p * ellSection.coefficient i p) * qSection.coefficient i p = _
  rw [pow_two]

theorem sigmaSection_value (p : Fiber 0) :
    (show ℂ from sectionValue sigmaSection p) =
      (show ℂ from sectionValue ellSection p)^2 * (show ℂ from sectionValue qSection p) := by
  rw [pow_two]
  rfl

/-- The actual section map is the fibrewise product ℓ²Q. -/
theorem sigmaSection_product_sectionMap (p : Fiber 0) :
    sectionMap sigmaSection p = ⟨p,
      (show ℂ from sectionValue ellSection p)^2 * (show ℂ from sectionValue qSection p)⟩ := by
  exact congrArg (fun z => Bundle.TotalSpace.mk p z) (sigmaSection_value p)

theorem sigmaSection_analytic :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (sectionMap sigmaSection) := sectionMap_contMDiff _

theorem sigmaSection_witness_ne_zero : sectionValue sigmaSection auxiliaryWitness ≠ 0 := by
  intro hz
  exact (mul_ne_zero (pow_ne_zero 2 ellSection_witness_ne_zero) qSection_witness_ne_zero)
    ((sigmaSection_value auxiliaryWitness).symm.trans hz)

theorem sigmaSection_nonzero : ∃ p : Fiber 0, sectionValue sigmaSection p ≠ 0 :=
  ⟨auxiliaryWitness,sigmaSection_witness_ne_zero⟩

def sigmaHomogeneous : FailureOfSemipositiveMetricExtension.GlobalLineBundle.HomogeneousData 5 where
  value q := (q.2 2)^2 * (q.2 0 * q.2 1 * (q.2 0-q.2 1))
  analytic := by fun_prop
  homogeneous t c v := by simp [Pi.smul_apply,smul_eq_mul,zpow_ofNat]; ring

def sigmaDenominator : SectionData 0 12 (fun _ => -3) where
  coefficient := (multiplySections (multiplySections ellDenominator ellDenominator) qDenominator).coefficient
  analytic := (multiplySections (multiplySections ellDenominator ellDenominator) qDenominator).analytic
  compatible i j p hp := by
    have h := (multiplySections (multiplySections ellDenominator ellDenominator) qDenominator).compatible i j p hp
    have hb : (fun r => (-ellDegree r + -ellDegree r) + -qDegree r) =
        (fun _ : Fin 4 => (-3 : ℤ)) := by
      funext r
      fin_cases r <;> decide
    change gain 0 12 _ i j p * _ = _ at h
    conv at h => lhs; arg 1; rw [hb]
    exact h

def sigmaNumerator : SectionData 0 ((-7:ℤ)+12) (fun _ => (3:ℤ)+(-3)) where
  coefficient := (homogeneousSection 0 sigmaHomogeneous).coefficient
  analytic := (homogeneousSection 0 sigmaHomogeneous).analytic
  compatible i j p hp := by convert (homogeneousSection 0 sigmaHomogeneous).compatible i j p hp using 1

theorem sigmaNumerator_coefficient (i : Index) (p : Fiber 0) :
    sigmaNumerator.coefficient i p =
      (ellNumerator.coefficient i p)^2 * qNumerator.coefficient i p := rfl

/-- Before exceptional division, σ is exactly the prescribed quintic z²xy(x-y). -/
theorem sigmaSection_division (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    sigmaSection.coefficient i p * sigmaDenominator.coefficient i p = sigmaNumerator.coefficient i p := by
  have hE := ellDivisionData.quotientSection_division i p hp
  have hQ := qDivisionData.quotientSection_division i p hp
  change ellSection.coefficient i p * ellDenominator.coefficient i p = ellNumerator.coefficient i p at hE
  change qSection.coefficient i p * qDenominator.coefficient i p = qNumerator.coefficient i p at hQ
  change ((ellSection.coefficient i p * ellSection.coefficient i p) * qSection.coefficient i p) *
    ((ellDenominator.coefficient i p * ellDenominator.coefficient i p) * qDenominator.coefficient i p) = _
  calc
    _ = (ellSection.coefficient i p * ellDenominator.coefficient i p)^2 *
        (qSection.coefficient i p * qDenominator.coefficient i p) := by ring
    _ = _ := by rw [hE,hQ,sigmaNumerator_coefficient]

/-- The actual section maps satisfy the global quintic division identity. -/
theorem sigmaSection_division_sectionMap :
    sectionMap (multiplySections sigmaSection sigmaDenominator) = sectionMap sigmaNumerator := by
  funext p
  apply congrArg (fun z => Bundle.TotalSpace.mk p z)
  exact sigmaSection_division ((core 0 ((-7:ℤ)+12) (fun _ => (3:ℤ)+(-3))).indexAt p) p
    ((core 0 ((-7:ℤ)+12) (fun _ => (3:ℤ)+(-3))).mem_baseSet_at p)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
