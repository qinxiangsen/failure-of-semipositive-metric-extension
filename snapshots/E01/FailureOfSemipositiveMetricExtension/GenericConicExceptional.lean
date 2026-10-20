import FailureOfSemipositiveMetricExtension.GenericConicPencilMapping

/-! The divided pencil on each genuine exceptional projective line is an
explicit projective linear automorphism for t != 0. This prevents additional
exceptional points in a generic pencil fibre. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set

def exceptionalLinear (t : ℂ) (r : Fin 4) : Blowup.Plane →ₗ[ℂ] Blowup.Plane where
  toFun v := match r with
    | 0 => ![v 1-t*v 0,-t*v 0]
    | 1 => ![-t*v 0,v 1-t*v 0]
    | 2 => ![v 1-t*v 0,v 1]
    | 3 => v
  map_add' u v := by fin_cases r <;> ext k <;> fin_cases k <;> simp <;> ring
  map_smul' a v := by fin_cases r <;> ext k <;> fin_cases k <;> simp <;> ring

theorem exceptionalLinear_eq_zero (t : ℂ) (ht : t ≠ 0) (r : Fin 4) (v : Blowup.Plane)
    (h : exceptionalLinear t r v = 0) : v = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases r
  · have hv : v 0 = 0 := by simpa [exceptionalLinear,ht] using h1
    have hw : v 1 = 0 := by simpa [exceptionalLinear,hv] using h0
    ext k; fin_cases k <;> assumption
  · have hv : v 0 = 0 := by simpa [exceptionalLinear,ht] using h0
    have hw : v 1 = 0 := by simpa [exceptionalLinear,hv] using h1
    ext k; fin_cases k <;> assumption
  · have hw : v 1 = 0 := h1
    have hv : v 0 = 0 := by simpa [exceptionalLinear,hw,ht] using h0
    ext k; fin_cases k <;> assumption
  · exact h

theorem exceptionalLinear_injective (t : ℂ) (ht : t ≠ 0) (r : Fin 4) :
    Function.Injective (exceptionalLinear t r) := by
  intro v w h
  apply sub_eq_zero.mp
  apply exceptionalLinear_eq_zero t ht r
  rw [map_sub,h,sub_self]

def centreParam (t : ℂ) (r : Fin 4) (d : Direction) : Fiber t :=
  ⟨((pointOverCentre r t d).val.1,(pointOverCentre r t d).val.2.1),(pointOverCentre r t d).property⟩

@[simp] theorem inclusion_centreParam (t : ℂ) (r : Fin 4) (d : Direction) :
    FixedFiber.inclusion t (centreParam t r d) = pointOverCentre r t d := rfl

@[simp] theorem centreParam_param (t : ℂ) (r : Fin 4) (e : Fin 2) (s : ℂ) :
    centreParam t r (ProjectiveLine.param e s) = FixedFiber.param t r e (0,s) := by
  apply FixedFiber.inclusion_injective t
  rw [inclusion_centreParam,FixedFiber.inclusion_param,chartParam_exceptional]

theorem pencilMap_centreParam (t : ℂ) (ht : t ≠ 0) (r : Fin 4) (d : Direction) :
    pencilMap t (centreParam t r d) =
      Projectivization.map (exceptionalLinear t r) (exceptionalLinear_injective t ht r) d := by
  obtain ⟨e,s,rfl⟩ := ProjectiveLine.charts_cover d
  rw [centreParam_param,NearbyPencil.pencilMap_param t r e (0,s) (exceptional_mem_chartDomain r e s t)]
  rw [ProjectiveLine.param_eq_mk_sourceVector]
  have hv : (fun k => GlobalLineBundle.pencilLocalCoefficient r e k ((0,s),t)) =
      exceptionalLinear t r (ProjectiveLine.sourceVector e s) := by
    fin_cases r <;> fin_cases e <;> ext k <;> fin_cases k <;>
      simp [GlobalLineBundle.pencilLocalCoefficient,PencilSections.x₁,PencilSections.y₁,
        PencilSections.x₂,PencilSections.y₂,PencilSections.x₃,PencilSections.y₃,
        PencilSections.x₄,PencilSections.y₄,exceptionalLinear,ProjectiveLine.sourceVector,
        Blowup.vectorX,Blowup.vectorY]
  rw [hv,ProjectiveLine.vectorPoint_eq_mk _
    (fun h => ProjectiveLine.sourceVector_ne_zero e s (exceptionalLinear_eq_zero t ht r _ h))]
  rfl

theorem centreParam_of_base (t : ℂ) (r : Fin 4) (p : Fiber t)
    (hp : FixedFiber.blowdown t p = centre r t) :
    centreParam t r (FixedFiber.direction t r p) = p := by
  apply FixedFiber.inclusion_injective t
  exact congrArg Subtype.val ((exceptionalFiberEquiv r t).left_inv
    ⟨FixedFiber.inclusion t p,⟨hp,rfl⟩⟩)

/-- The true pencil is injective on each individual exceptional curve. -/
theorem pencilMap_injective_on_centre (t : ℂ) (ht : t ≠ 0) (r : Fin 4) (p q : Fiber t)
    (hp : FixedFiber.blowdown t p = centre r t) (hq : FixedFiber.blowdown t q = centre r t)
    (h : pencilMap t p = pencilMap t q) : p = q := by
  have hmap : Projectivization.map (exceptionalLinear t r) (exceptionalLinear_injective t ht r)
      (FixedFiber.direction t r p) =
      Projectivization.map (exceptionalLinear t r) (exceptionalLinear_injective t ht r)
      (FixedFiber.direction t r q) := by
    rw [← pencilMap_centreParam t ht r (FixedFiber.direction t r p),
      ← pencilMap_centreParam t ht r (FixedFiber.direction t r q),
      centreParam_of_base t r p hp,centreParam_of_base t r q hq]
    exact h
  have hd := Projectivization.map_injective (exceptionalLinear t r) (exceptionalLinear_injective t ht r) hmap
  rw [← centreParam_of_base t r p hp,← centreParam_of_base t r q hq,hd]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
