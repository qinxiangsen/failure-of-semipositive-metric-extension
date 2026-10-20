import FailureOfSemipositiveMetricExtension.CentralEllGermDivision
import FailureOfSemipositiveMetricExtension.CentralHolomorphicResidualVanishing

/-! The first three central adjoint ambient systems with their genuine divisor
stalk condition vanish. Local ideal membership is converted into an actual
holomorphic residual section before the geometric vanishing theorem is applied. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem zero_of_divideByEll_zero {a : ℤ} {b : Fin 4 → ℤ}
    (N : SectionData 0 (a+(-2)) (fun r => b r+ellDegree r))
    (hN : ∀ i p hp, sectionGerm N i p hp ∈ ellPowerStalkIdeal 1 p)
    (hz : ∀ p, Holomorphic.sectionValue (divideByEll N hN) p = 0) (p : Fiber 0) :
    sectionValue N p = 0 := by
  let i := (core 0 (a+(-2)) (fun r => b r+ellDegree r)).indexAt p
  have hi := (core 0 (a+(-2)) (fun r => b r+ellDegree r)).mem_baseSet_at p
  have hc := (Holomorphic.sectionValue_zero_iff (divideByEll N hN) i p hi).mp (hz p)
  have he := divideByEll_coefficient_mul N hN i p hi
  rw [hc,zero_mul] at he
  exact he.symm

def secondResidualDegree (r : Fin 4) : ℤ := if r = 3 then 1 else 0
def thirdResidualDegree (r : Fin 4) : ℤ := if r = 3 then 2 else 1

theorem secondResidual_degree_add : (fun r => secondResidualDegree r + ellDegree r) = (fun _ => (1:ℤ)) := by
  funext r
  fin_cases r <;> decide

theorem thirdResidual_degree_add : (fun r => thirdResidualDegree r + ellDegree r) = (fun _ => (2:ℤ)) := by
  funext r
  fin_cases r <;> decide

def secondEllNumerator (N : SectionData 0 (-3) (fun _ => 1)) :
    SectionData 0 ((-1)+(-2)) (fun r => secondResidualDegree r + ellDegree r) where
  coefficient := N.coefficient
  analytic := N.analytic
  compatible i j p hp := by
    simpa only [secondResidual_degree_add,show (-1:ℤ)+(-2) = -3 by decide] using N.compatible i j p hp

def thirdEllNumerator (N : SectionData 0 (-5) (fun _ => 2)) :
    SectionData 0 ((-3)+(-2)) (fun r => thirdResidualDegree r + ellDegree r) where
  coefficient := N.coefficient
  analytic := N.analytic
  compatible i j p hp := by
    simpa only [thirdResidual_degree_add,show (-3:ℤ)+(-2) = -5 by decide] using N.compatible i j p hp

theorem central_first_ambient_section_zero (N : SectionData 0 (-1) (fun _ => 0)) (p : Fiber 0) :
    sectionValue N p = 0 :=
  CentralLine.residual_one_section_zero (sectionValue N) (sectionMap_contMDiff N) p

theorem central_second_ambient_stalk_section_zero (N : SectionData 0 (-3) (fun _ => 1))
    (hN : ∀ i p hp, sectionGerm N i p hp ∈ ellPowerStalkIdeal 1 p) (p : Fiber 0) :
    sectionValue N p = 0 := by
  let R := secondEllNumerator N
  have hR : ∀ i p hp, sectionGerm R i p hp ∈ ellPowerStalkIdeal 1 p := hN
  have hz : ∀ p, Holomorphic.sectionValue (divideByEll R hR) p = 0 :=
    CentralLine.Holomorphic.residual_two_section_zero
      (Holomorphic.sectionValue (divideByEll R hR)) (Holomorphic.sectionMap_contMDiff _) 
  have hv := zero_of_divideByEll_zero R hR hz p
  apply (sectionValue_zero_iff N ((core 0 ((-1)+(-2))
    (fun r => secondResidualDegree r+ellDegree r)).indexAt p) p
      ((core 0 ((-1)+(-2)) (fun r => secondResidualDegree r+ellDegree r)).mem_baseSet_at p)).mpr
  exact hv

theorem central_third_ambient_stalk_section_zero (N : SectionData 0 (-5) (fun _ => 2))
    (hN : ∀ i p hp, sectionGerm N i p hp ∈ ellPowerStalkIdeal 1 p) (p : Fiber 0) :
    sectionValue N p = 0 := by
  let R := thirdEllNumerator N
  have hR : ∀ i p hp, sectionGerm R i p hp ∈ ellPowerStalkIdeal 1 p := hN
  have hz : ∀ p, Holomorphic.sectionValue (divideByEll R hR) p = 0 :=
    CentralLine.Holomorphic.residual_three_section_zero
      (Holomorphic.sectionValue (divideByEll R hR)) (Holomorphic.sectionMap_contMDiff _)
  have hv := zero_of_divideByEll_zero R hR hz p
  apply (sectionValue_zero_iff N ((core 0 ((-3)+(-2))
    (fun r => thirdResidualDegree r+ellDegree r)).indexAt p) p
      ((core 0 ((-3)+(-2)) (fun r => thirdResidualDegree r+ellDegree r)).mem_baseSet_at p)).mpr
  exact hv

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
